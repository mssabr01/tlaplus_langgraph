"""Wrapper around the Claude Agent SDK for synchronous pipeline usage.

Authentication: Uses OAuth credentials from `claude auth login`.
Do NOT set ANTHROPIC_API_KEY — that would route to the paid API
instead of your subscription quota.

Works around SDK bug: rate_limit_event crash (issue #472).
"""

import asyncio
import logging
import os
import sys
from typing import Optional

from claude_agent_sdk import (
    query,
    ClaudeAgentOptions,
    AssistantMessage,
    ResultMessage,
)
from claude_agent_sdk._errors import MessageParseError

logger = logging.getLogger(__name__)

# ---------------------------------------------------------------------------
# Monkey-patch: skip unknown message types (SDK issue #472)
# ---------------------------------------------------------------------------
from claude_agent_sdk._internal import message_parser as _parser_mod
from claude_agent_sdk._internal import client as _client_mod

_original_parse = _parser_mod.parse_message


def _patched_parse(data):
    try:
        return _original_parse(data)
    except MessageParseError as e:
        if "Unknown message type" in str(e):
            logger.debug(f"Skipping unknown SDK message type: {e}")
            return None
        raise


_parser_mod.parse_message = _patched_parse
if hasattr(_client_mod, "parse_message"):
    _client_mod.parse_message = _patched_parse
for name, mod in list(sys.modules.items()):
    if name.startswith("claude_agent_sdk") and mod is not None:
        if getattr(mod, "parse_message", None) is _original_parse:
            mod.parse_message = _patched_parse

# ---------------------------------------------------------------------------
# Configuration
# ---------------------------------------------------------------------------
DEFAULT_MODEL = os.environ.get("CLAUDE_MODEL", "claude-sonnet-4-5")
MAX_RETRIES = int(os.environ.get("CLAUDE_MAX_RETRIES", "5"))
RETRY_DELAY = int(os.environ.get("CLAUDE_RETRY_DELAY", "60"))


class _RateLimitHit(Exception):
    pass


AGENT_WORKSPACE = "/tmp/pipeline_workspace"


async def _call_async(
    prompt: str,
    system_prompt: Optional[str] = None,
    max_turns: Optional[int] = None,
    model: Optional[str] = None,
    cwd: Optional[str] = None,
    allowed_tools: Optional[list[str]] = None,
) -> str:
    """Async implementation with retry on rate limits.

    To avoid ARG_MAX overflow, the system_prompt is written to a file
    and the user prompt is prefixed with instructions to read it.
    """
    last_error = None

    # Write system prompt to file so it doesn't bloat CLI args
    effective_prompt = prompt
    if system_prompt:
        os.makedirs(AGENT_WORKSPACE, exist_ok=True)
        import hashlib
        sp_hash = hashlib.md5(system_prompt[:200].encode()).hexdigest()[:8]
        sp_path = os.path.join(AGENT_WORKSPACE, f"_system_prompt_{sp_hash}.md")
        with open(sp_path, "w") as f:
            f.write(system_prompt)
        effective_prompt = (
            f"IMPORTANT: First read your role instructions at {sp_path} — "
            f"follow them precisely.\n\n{prompt}"
        )

    # Log prompt size to help debug any remaining ARG_MAX issues
    logger.info(f"Effective prompt size: {len(effective_prompt)} chars")

    for attempt in range(1, MAX_RETRIES + 1):
        response_parts: list[str] = []

        options = ClaudeAgentOptions(
            max_turns=max_turns,
            model=model or DEFAULT_MODEL,
        )
        if cwd:
            options.cwd = cwd
        # Always allow Read so the agent can read its system prompt file
        tools = list(allowed_tools) if allowed_tools else []
        if "Read" not in tools:
            tools.append("Read")
        options.allowed_tools = tools

        try:
            async for message in query(prompt=effective_prompt, options=options):
                if message is None:
                    continue

                msg_type = type(message).__name__
                logger.info(f"SDK message type: {msg_type}")

                if isinstance(message, AssistantMessage):
                    if hasattr(message, "error") and message.error:
                        error_type = message.error
                        logger.warning(f"API error in stream: {error_type}")
                        if error_type == "rate_limit":
                            raise _RateLimitHit()
                        continue
                    for block in message.content:
                        # Try attribute access (SDK object)
                        text = getattr(block, "text", None)
                        # Try dict access (raw dict block)
                        if text is None and isinstance(block, dict):
                            text = block.get("text")
                        if text:
                            logger.info(
                                f"Captured text block ({len(text)} chars): "
                                f"{text[:80]}..."
                            )
                            response_parts.append(text)
                        else:
                            block_type = getattr(block, "type", None) or (
                                block.get("type") if isinstance(block, dict) else None
                            )
                            logger.info(f"Non-text content block: type={block_type}")

                elif isinstance(message, ResultMessage):
                    logger.info(
                        f"SDK result: turns={message.num_turns}, "
                        f"duration={message.duration_ms}ms, "
                        f"cost=${message.total_cost_usd}"
                    )
                    # Try multiple ways to get the result text
                    result_text = getattr(message, "result", None)
                    if result_text:
                        logger.info(
                            f"ResultMessage.result ({len(result_text)} chars): "
                            f"{result_text[:80]}..."
                        )
                        response_parts.append(result_text)
                    else:
                        # Log all attributes for debugging
                        attrs = [a for a in dir(message) if not a.startswith("_")]
                        logger.warning(
                            f"ResultMessage.result is empty. "
                            f"Available attrs: {attrs}"
                        )
                else:
                    # Log ALL attributes of unknown message types for debugging
                    attrs = {
                        a: repr(getattr(message, a, None))[:200]
                        for a in dir(message)
                        if not a.startswith("_")
                    }
                    logger.info(f"Unhandled message type: {msg_type}, attrs={attrs}")

            result = "\n".join(response_parts).strip()
            if result:
                return result

            if not response_parts:
                last_error = "empty_response"
                logger.warning(f"Empty response on attempt {attempt}")

        except _RateLimitHit:
            last_error = "rate_limit"
            logger.warning(f"Rate limit hit on attempt {attempt}")
        except MessageParseError as e:
            last_error = str(e)
            logger.warning(f"SDK parse error (attempt {attempt}): {e}")

        if attempt < MAX_RETRIES:
            wait = RETRY_DELAY * attempt
            logger.info(f"Waiting {wait}s before retry {attempt + 1}/{MAX_RETRIES}...")
            await asyncio.sleep(wait)

    raise RuntimeError(
        f"Claude SDK failed after {MAX_RETRIES} attempts. Last error: {last_error}"
    )


def call_claude_code(
    prompt: str,
    system_prompt: Optional[str] = None,
    max_turns: Optional[int] = None,
    model: Optional[str] = None,
    cwd: Optional[str] = None,
    allowed_tools: Optional[list[str]] = None,
) -> str:
    """Call Claude Code SDK and return the text response.

    IMPORTANT: Keep prompt under ~80K chars to avoid OS ARG_MAX limits.
    For large content, write to files and reference paths in the prompt.

    Args:
        prompt: The user prompt.
        system_prompt: System prompt configuring Claude's role.
        max_turns: Maximum agentic turns (multi-step tool use rounds).
        model: Model to use (default: CLAUDE_MODEL env var).
        cwd: Working directory for the Claude subprocess.
        allowed_tools: Tools the sub-agent can use (e.g. ["Read"]).

    Returns:
        The assistant's text response as a single string.
    """
    try:
        loop = asyncio.get_running_loop()
    except RuntimeError:
        loop = None

    if loop and loop.is_running():
        import concurrent.futures
        with concurrent.futures.ThreadPoolExecutor() as pool:
            result = pool.submit(
                asyncio.run,
                _call_async(prompt, system_prompt, max_turns, model, cwd, allowed_tools),
            ).result()
        return result
    else:
        return asyncio.run(
            _call_async(prompt, system_prompt, max_turns, model, cwd, allowed_tools)
        )

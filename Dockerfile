FROM python:3.12-slim

# ============================================================
# TLA+ Specification Agent Pipeline
# LangGraph + TLC Model Checker + Claude Code
# ============================================================

# Avoid interactive prompts during package installation
ENV DEBIAN_FRONTEND=noninteractive

# --- System dependencies ---
RUN apt-get update && apt-get install -y --no-install-recommends \
    # Java 21 for TLC model checker (requires 11+; 17 unavailable on Trixie)
    openjdk-21-jre-headless \
    # Claude Code native installer + general utilities
    curl \
    git \
    # Build essentials for Python packages
    build-essential \
    && rm -rf /var/lib/apt/lists/*

# --- TLA+ Tools (TLC model checker, PlusCal translator, SANY parser) ---
ENV TLA_VERSION=1.8.0
ENV TLA_HOME=/opt/tla
RUN mkdir -p ${TLA_HOME} && \
    curl -fsSL "https://github.com/tlaplus/tlaplus/releases/download/v${TLA_VERSION}/tla2tools.jar" \
    -o ${TLA_HOME}/tla2tools.jar

# Convenience wrapper scripts
RUN echo '#!/bin/bash\njava -cp /opt/tla/tla2tools.jar tlc2.TLC "$@"' > /usr/local/bin/tlc && \
    chmod +x /usr/local/bin/tlc && \
    echo '#!/bin/bash\njava -cp /opt/tla/tla2tools.jar pcal.trans "$@"' > /usr/local/bin/pcal && \
    chmod +x /usr/local/bin/pcal && \
    echo '#!/bin/bash\njava -cp /opt/tla/tla2tools.jar tla2sany.SANY "$@"' > /usr/local/bin/sany && \
    chmod +x /usr/local/bin/sany

ENV CLASSPATH=${TLA_HOME}/tla2tools.jar:${CLASSPATH}

# --- Node.js 22 (required runtime for Claude Code CLI bundled in the SDK) ---
RUN curl -fsSL https://deb.nodesource.com/setup_22.x | bash - && \
    apt-get install -y --no-install-recommends nodejs && \
    rm -rf /var/lib/apt/lists/*

# --- Python dependencies (claude-agent-sdk bundles the Claude Code CLI) ---
COPY requirements.txt /tmp/requirements.txt
RUN pip install --no-cache-dir -r /tmp/requirements.txt && \
    rm /tmp/requirements.txt

# --- Ensure bundled claude CLI is on PATH ---
RUN CLAUDE_BIN=$(find /usr/local/lib/python3.12 -name "claude" -type f 2>/dev/null | head -1) && \
    if [ -n "$CLAUDE_BIN" ]; then ln -sf "$CLAUDE_BIN" /usr/local/bin/claude; fi
# Fallback: install Claude Code via npm if SDK didn't bundle a working binary
RUN claude --version || npm install -g @anthropic-ai/claude-code

# --- Pre-approve tool permissions so Claude sub-agents don't hang waiting ---
RUN mkdir -p /root/.claude && \
    echo '{"permissions":{"allow":["Read","Glob","Grep","Write"],"deny":[]}}' \
    > /root/.claude/settings.json && \
    mkdir -p /tmp/pipeline_workspace/.claude && \
    cp /root/.claude/settings.json /tmp/pipeline_workspace/.claude/settings.json

# --- Copy workspace code ---
COPY workspace/pipeline/ /workspace/pipeline/
COPY workspace/evals/ /workspace/evals/
COPY workspace/exemplars/ /workspace/exemplars/

WORKDIR /workspace

# Default: run pipeline against the docs directory
CMD ["python", "pipeline/main.py", "docs/", "specs/", "exemplars/"]
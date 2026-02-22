FROM python:3.12-slim

# ============================================================
# TLA+ Specification Agent Pipeline
# LangGraph + TLC Model Checker + Claude Code
# ============================================================

# Avoid interactive prompts during package installation
ENV DEBIAN_FRONTEND=noninteractive

# --- System dependencies ---
RUN apt-get update && apt-get install -y --no-install-recommends \
    # Java 17 for TLC model checker (requires 11+)
    openjdk-17-jre-headless \
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

# --- Claude Code (native installer) ---
RUN curl -fsSL https://claude.ai/install.sh | bash
ENV PATH="/root/.claude/bin:${PATH}"

# --- Python dependencies ---
COPY requirements.txt /tmp/requirements.txt
RUN pip install --no-cache-dir -r /tmp/requirements.txt && \
    rm /tmp/requirements.txt

# --- Copy pipeline code ---
COPY pipeline/ /workspace/pipeline/

WORKDIR /workspace

CMD ["python", "pipeline/main.py"]
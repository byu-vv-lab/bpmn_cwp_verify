# ============================================================================
# Base stage: Common setup (Spin binary + gcc for Lambda compatibility)
# ============================================================================
FROM public.ecr.aws/lambda/python:3.12 AS base

# Install build tools and runtime dependencies
# bison provides yacc (needed to build Spin)
# Create yacc wrapper that uses bison -y for yacc compatibility
RUN microdnf -y install gcc make tar gzip ca-certificates zip which wget bison \
    && microdnf -y clean all \
    && printf '#!/usr/bin/bash\nexec /usr/bin/bison -y "$@"\n' > /usr/bin/yacc \
    && chmod +x /usr/bin/yacc \
    && ls -la /usr/bin/yacc && cat /usr/bin/yacc

ARG SPIN_VERSION=6.5.2

RUN wget https://github.com/nimble-code/Spin/archive/refs/tags/version-${SPIN_VERSION}.tar.gz && \
    tar -xzf version-${SPIN_VERSION}.tar.gz && \
    cd Spin-version-${SPIN_VERSION}/Src && \
    make && \
    mkdir -p /opt/bin && \
    cp spin /opt/bin/spin && \
    chmod +x /opt/bin/spin && \
    strip /opt/bin/spin && \
    cd / && \
    rm -rf Spin-version-${SPIN_VERSION} version-${SPIN_VERSION}.tar.gz

# Ensure Spin is on PATH
ENV PATH=/opt/bin:$PATH

# ============================================================================
# Development stage: For local development with hot reload
# ============================================================================
FROM base AS dev

WORKDIR /app

# Install Python package in editable mode (for development)
COPY pyproject.toml ./
COPY src ./src
RUN pip install --no-cache-dir -e ".[dev]"

# Default command (can be overridden)
CMD ["/bin/bash"]

# ============================================================================
# Lambda stage: For AWS Lambda deployment
# ============================================================================
FROM base AS lambda

WORKDIR /var/task

# Install Python package (production mode)
COPY pyproject.toml ./
COPY src ./src
RUN pip install --no-cache-dir .

# Copy Lambda handler
COPY lambda_function.py .

# Lambda handler entry point
CMD [ "lambda_function.lambda_handler" ]

# ============================================================================
# Spin Layer stage: Build a Lambda layer with just Spin binary
# ============================================================================
FROM base AS spin-layer

# Create layer structure
RUN mkdir -p /out && \
    cd /opt && \
    zip -rq9 /out/spin-layer.zip .

# Minimal final stage just to hold the artifact
FROM scratch AS artifact
COPY --from=spin-layer /out/spin-layer.zip /spin-layer.zip

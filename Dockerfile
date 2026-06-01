# ============================================================================
# Base stage: Common setup (Spin + CBMC + gcc for Lambda compatibility)
# Both dev and lambda extend this stage — they stay in sync automatically.
# ============================================================================
FROM public.ecr.aws/lambda/python:3.12 AS base

# Install build tools and runtime dependencies
# bison provides yacc (needed to build Spin and CBMC)
# cmake + gcc-c++ + flex are needed to build CBMC from source
# (no pre-built CBMC binary exists for Amazon Linux)
RUN microdnf -y install gcc gcc-c++ make cmake tar gzip xz ca-certificates zip which wget bison flex git patch \
    && microdnf -y clean all \
    && printf '#!/usr/bin/bash\nexec /usr/bin/bison -y "$@"\n' > /usr/bin/yacc \
    && chmod +x /usr/bin/yacc

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

ARG CBMC_VERSION=6.9.0

# Build CBMC from source. -DWITH_JBMC=OFF skips the Java BMC component,
# avoiding a Java dependency and keeping the image smaller.
RUN git clone --depth 1 --branch cbmc-${CBMC_VERSION} \
        https://github.com/diffblue/cbmc.git /tmp/cbmc && \
    cd /tmp/cbmc && \
    git submodule update --init && \
    cmake -S . -B build \
          -DCMAKE_BUILD_TYPE=Release \
          -DWITH_JBMC=OFF && \
    cmake --build build --target cbmc -j$(nproc) && \
    cp build/bin/cbmc /opt/bin/cbmc && \
    rm -rf /tmp/cbmc

# Ensure Spin and CBMC are on PATH
ENV PATH=/opt/bin:$PATH

# ============================================================================
# Development stage: Adds Node.js (pyright) and installs the package in
# editable mode on top of base. Dev and lambda use the same base so their
# Spin/CBMC binaries are always identical.
# ============================================================================
FROM base AS dev

# Install Node.js (needed for pyright and other tooling)
ARG NODE_VERSION=16.20.2
ARG TARGETARCH
RUN case "${TARGETARCH}" in \
        "amd64") NODE_ARCH="x64" ;; \
        "arm64") NODE_ARCH="arm64" ;; \
        *) echo "Unsupported TARGETARCH ${TARGETARCH}" && exit 1 ;; \
    esac \
    && NODE_DIST="node-v${NODE_VERSION}-linux-${NODE_ARCH}" \
    && wget -q https://nodejs.org/dist/v${NODE_VERSION}/${NODE_DIST}.tar.xz \
    && mkdir -p /usr/local/lib/nodejs \
    && tar -xJf ${NODE_DIST}.tar.xz -C /usr/local/lib/nodejs \
    && rm ${NODE_DIST}.tar.xz \
    && ln -sf /usr/local/lib/nodejs/${NODE_DIST}/bin/node /usr/local/bin/node \
    && ln -sf /usr/local/lib/nodejs/${NODE_DIST}/bin/npm /usr/local/bin/npm \
    && ln -sf /usr/local/lib/nodejs/${NODE_DIST}/bin/npx /usr/local/bin/npx \
    && ln -sf /usr/local/lib/nodejs/${NODE_DIST}/bin/corepack /usr/local/bin/corepack

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

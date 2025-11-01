FROM public.ecr.aws/lambda/python:3.12 AS builder

# Build tools for Spin (Amazon Linux 2023 uses microdnf)
RUN microdnf -y install gcc make tar gzip ca-certificates zip \
    && microdnf -y clean all

ARG SPIN_VERSION=6.5.3

# Build Spin from source and stage a Lambda layer layout
RUN set -eux; \
  curl -L -o /tmp/spin.tar.gz \
    "https://github.com/nimble-code/Spin/archive/refs/tags/version-${SPIN_VERSION}.tar.gz"; \
  mkdir -p /tmp/spin-src; \
  tar -xzf /tmp/spin.tar.gz -C /tmp/spin-src --strip-components=1; \
  cd /tmp/spin-src/Src${SPIN_VERSION}; \
  make -f makefile; \
  install -m 0755 spin /opt/bin/spin; \
  cd /; \
  mkdir -p /out; \
  cd /opt; \
  zip -rq9 /out/spin-layer.zip .

# Minimal final stage just to hold the artifact
FROM scratch AS artifact
COPY --from=builder /out/spin-layer.zip /spin-layer.zip

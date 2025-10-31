# Builder: compile Spin
ARG SPIN_VERSION=6.5.2
FROM public.ecr.aws/lambda/python:3.12 AS spin-builder
ARG SPIN_VERSION

# Build deps only in builder
RUN dnf install -y gcc make byacc flex wget tar gzip glibc-devel \
  && dnf clean all && rm -rf /var/cache/dnf

WORKDIR /tmp
# Optional: add and verify checksum for security
# ARG SPIN_SHA256=<insert_sha256_here>
RUN set -eux; \
  wget -O spin.tar.gz "https://github.com/nimble-code/Spin/archive/refs/tags/version-${SPIN_VERSION}.tar.gz"; \
  tar -xzf spin.tar.gz; \
  cd "Spin-version-${SPIN_VERSION}/Src"; \
  make; \
  strip spin; \
  install -Dm755 spin /opt/bin/spin

# Optional: prebuild a generic pan to avoid gcc in final image
# RUN set -eux; cd "Spin-version-${SPIN_VERSION}/Src"; \
#   ./spin -a model.pml  # generate pan.c from a placeholder if your flow allows
#   gcc -O2 -o /opt/bin/pan pan.c; strip /opt/bin/pan

# Final: minimal Lambda image
FROM public.ecr.aws/lambda/python:3.12

# If you truly need gcc at runtime (avoid if possible):
# RUN dnf install -y gcc glibc-devel \
#   && dnf clean all && rm -rf /var/cache/dnf

ENV PATH="/opt/bin:${PATH}"
WORKDIR ${LAMBDA_TASK_ROOT}

# Bring in Spin (and optionally pan) only
COPY --from=spin-builder /opt/bin/spin /opt/bin/
# COPY --from=spin-builder /opt/bin/pan /opt/bin/

# Optional: quick verification
RUN /opt/bin/spin -V

# Copy your function code here if needed
# COPY . ${LAMBDA_TASK_ROOT}
# CMD ["lambda_function.handler"]

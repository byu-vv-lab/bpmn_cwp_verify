#!/bin/sh

# Amazon Linux 2023 uses microdnf instead of apt
# Install JRE for ANTLRv4 tools and graphviz binaries
sudo microdnf -y update
sudo microdnf -y install java-17-amazon-corretto graphviz
sudo microdnf -y clean all

# Spin is already installed in /opt/bin/spin from the base Dockerfile stage
# Verify it's available
spin -V || echo "Warning: Spin not found in PATH"

# Upgrade pip
pip install --upgrade pip

# Install pyright for pre-commit
pip install pyright

# Install the package
pip install --user --editable ".[dev]"

# Install pyright
npm install -g pyright

# Install pre-commit
pre-commit install

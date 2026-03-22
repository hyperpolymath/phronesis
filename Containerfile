# SPDX-License-Identifier: PMPL-1.0-or-later
# Multi-stage Dockerfile for Phronesis production deployment

# ============================================================
# Stage 1: Build
# ============================================================
FROM hexpm/elixir:1.16.0-erlang-26.2.1-alpine-3.19.0 AS build

# Install build dependencies
RUN apk add --no-cache \
    git \
    build-base \
    nodejs \
    npm

# Set working directory
WORKDIR /app

# Install hex and rebar
RUN mix local.hex --force && \
    mix local.rebar --force

# Copy dependency files
COPY mix.exs mix.lock ./

# Install dependencies
ENV MIX_ENV=prod
RUN mix deps.get --only prod && \
    mix deps.compile

# Copy source code
COPY lib ./lib
COPY priv ./priv
COPY syntax ./syntax
COPY examples ./examples
COPY docs ./docs
COPY SPEC.core.scm ./
COPY README.adoc ./

# Compile application
RUN mix compile

# Build release
RUN mix release

# ============================================================
# Stage 2: Runtime
# ============================================================
FROM alpine:3.19.0 AS runtime

# Install runtime dependencies
RUN apk add --no-cache \
    ncurses-libs \
    libstdc++ \
    libgcc \
    openssl

# Create app user
RUN addgroup -S phronesis && \
    adduser -S phronesis -G phronesis

# Set working directory
WORKDIR /app

# Copy release from build stage
COPY --from=build --chown=phronesis:phronesis /app/_build/prod/rel/phronesis ./

# Create directories for consensus data
RUN mkdir -p /app/priv/consensus_data && \
    chown -R phronesis:phronesis /app/priv

# Switch to app user
USER phronesis

# Expose ports
# 4369 - EPMD (Erlang Port Mapper Daemon)
# 9100-9200 - Erlang distribution ports
EXPOSE 4369 9100-9200

# Environment variables
ENV RELEASE_DISTRIBUTION=name
ENV RELEASE_NODE=phronesis@127.0.0.1
ENV PHRONESIS_CONSENSUS_ENABLED=false
ENV PHRONESIS_NODE_ID=node1

# Health check
HEALTHCHECK --interval=30s --timeout=3s --start-period=40s --retries=3 \
    CMD /app/bin/phronesis rpc "Application.started_applications() |> Enum.any?(fn {app, _, _} -> app == :phronesis end)" || exit 1

# Start the application
CMD ["/app/bin/phronesis", "start"]

FROM ubuntu:20.04

# Get ourselves ready to install packages (add universe repo)
RUN apt update
RUN apt install -y software-properties-common
RUN add-apt-repository universe

# Install packages
RUN apt install -y  \
    build-essential \
    curl            \
    libz3-dev

# Install and set up Rust
RUN curl https://sh.rustup.rs -sSf | sh -s -- -y
ENV PATH="/root/.cargo/bin:${PATH}"

COPY src src
COPY Cargo.toml Cargo.toml
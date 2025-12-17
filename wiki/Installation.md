# Installation

This guide covers installing Phronesis on various platforms.

---

## Requirements

### System Requirements
- **Erlang/OTP**: 25.0 or later
- **Elixir**: 1.14 or later
- **Operating System**: Linux, macOS, or Windows (WSL2)
- **Memory**: 512MB minimum, 2GB recommended
- **Disk**: 100MB for installation

### Optional Dependencies
- **Routinator** or **rpki-client**: For real RPKI validation
- **Git**: For version control integration

---

## Installation Methods

### Method 1: Pre-built Binaries (Recommended)

Download the latest release for your platform:

```bash
# Linux (x86_64)
curl -LO https://github.com/hyperpolymath/phronesis/releases/latest/download/phronesis-linux-amd64.tar.gz
tar xzf phronesis-linux-amd64.tar.gz
sudo mv phronesis /usr/local/bin/

# macOS (Apple Silicon)
curl -LO https://github.com/hyperpolymath/phronesis/releases/latest/download/phronesis-darwin-arm64.tar.gz
tar xzf phronesis-darwin-arm64.tar.gz
sudo mv phronesis /usr/local/bin/

# macOS (Intel)
curl -LO https://github.com/hyperpolymath/phronesis/releases/latest/download/phronesis-darwin-amd64.tar.gz
tar xzf phronesis-darwin-amd64.tar.gz
sudo mv phronesis /usr/local/bin/
```

Verify installation:

```bash
phronesis --version
# Phronesis 0.1.0
```

### Method 2: From Source

Clone and build from source:

```bash
# Clone repository
git clone https://github.com/hyperpolymath/phronesis.git
cd phronesis

# Install dependencies
mix deps.get

# Compile
mix compile

# Build escript
mix escript.build

# Install globally (optional)
sudo mv phronesis /usr/local/bin/
```

### Method 3: Mix Archive

Install as a Mix archive:

```bash
mix archive.install hex phronesis
```

### Method 4: Docker

Run in a container:

```bash
# Pull image
docker pull hyperpolymath/phronesis:latest

# Run interactively
docker run -it hyperpolymath/phronesis repl

# Run a policy file
docker run -v $(pwd):/policies hyperpolymath/phronesis run /policies/my_policy.phr
```

### Method 5: Nix

Using Nix flakes:

```bash
# Run directly
nix run github:hyperpolymath/phronesis

# Install to profile
nix profile install github:hyperpolymath/phronesis

# Development shell
nix develop github:hyperpolymath/phronesis
```

---

## Platform-Specific Instructions

### Linux

#### Ubuntu/Debian

```bash
# Install Erlang and Elixir
sudo apt update
sudo apt install erlang elixir

# Install from source
git clone https://github.com/hyperpolymath/phronesis.git
cd phronesis
mix deps.get
mix escript.build
sudo mv phronesis /usr/local/bin/
```

#### Fedora/RHEL

```bash
# Install Erlang and Elixir
sudo dnf install erlang elixir

# Install from source
git clone https://github.com/hyperpolymath/phronesis.git
cd phronesis
mix deps.get
mix escript.build
sudo mv phronesis /usr/local/bin/
```

#### Arch Linux

```bash
# Install from AUR (when available)
yay -S phronesis

# Or manually
sudo pacman -S erlang elixir
git clone https://github.com/hyperpolymath/phronesis.git
cd phronesis
mix deps.get
mix escript.build
sudo mv phronesis /usr/local/bin/
```

### macOS

#### Using Homebrew

```bash
# Install Erlang and Elixir
brew install erlang elixir

# Install Phronesis (when formula available)
brew install hyperpolymath/tap/phronesis

# Or from source
git clone https://github.com/hyperpolymath/phronesis.git
cd phronesis
mix deps.get
mix escript.build
mv phronesis /usr/local/bin/
```

### Windows

#### Using WSL2 (Recommended)

```powershell
# Enable WSL2
wsl --install

# In WSL, follow Linux instructions
```

#### Native (via Chocolatey)

```powershell
# Install Erlang and Elixir
choco install erlang elixir

# Clone and build
git clone https://github.com/hyperpolymath/phronesis.git
cd phronesis
mix deps.get
mix escript.build
```

---

## Post-Installation Setup

### 1. Verify Installation

```bash
# Check version
phronesis --version

# Run self-test
phronesis check --self-test

# Start REPL
phronesis repl
```

### 2. Configure Shell Completion

#### Bash

```bash
# Add to ~/.bashrc
eval "$(phronesis completions bash)"
```

#### Zsh

```bash
# Add to ~/.zshrc
eval "$(phronesis completions zsh)"
```

#### Fish

```bash
# Add to ~/.config/fish/config.fish
phronesis completions fish | source
```

### 3. Configure Editor

See [Tooling](CLI-Reference.md) for editor plugin installation.

### 4. Set Up RPKI Validator (Optional)

For real RPKI validation, install a validator:

```bash
# Install Routinator
cargo install routinator

# Or install rpki-client (OpenBSD origin)
# See: https://www.rpki-client.org/
```

Configure Phronesis to use it:

```bash
# In config/config.exs or environment
export PHRONESIS_RPKI_BACKEND=routinator
export PHRONESIS_RPKI_HOST=localhost
export PHRONESIS_RPKI_PORT=8323
```

---

## Troubleshooting

### Common Issues

#### "Command not found" after installation

Ensure `/usr/local/bin` is in your PATH:

```bash
echo $PATH
# Add if missing:
export PATH="/usr/local/bin:$PATH"
```

#### Erlang/Elixir version mismatch

Check versions:

```bash
erl -version
# Erlang (SMP,ASYNC_THREADS) (BEAM) emulator version 13.0

elixir --version
# Elixir 1.14.0 (compiled with Erlang/OTP 25)
```

Install correct versions using asdf:

```bash
asdf install erlang 25.0
asdf install elixir 1.14.0
asdf global erlang 25.0
asdf global elixir 1.14.0
```

#### Permission denied

```bash
# Fix executable permission
chmod +x /usr/local/bin/phronesis
```

#### Mix dependencies fail

```bash
# Clean and retry
mix deps.clean --all
mix deps.get
```

---

## Upgrading

### From Binary

```bash
# Download new version
curl -LO https://github.com/hyperpolymath/phronesis/releases/latest/download/phronesis-linux-amd64.tar.gz
tar xzf phronesis-linux-amd64.tar.gz
sudo mv phronesis /usr/local/bin/
```

### From Source

```bash
cd phronesis
git pull
mix deps.get
mix escript.build
sudo mv phronesis /usr/local/bin/
```

### Check for Updates

```bash
phronesis --check-update
```

---

## Uninstalling

### Binary Installation

```bash
sudo rm /usr/local/bin/phronesis
```

### Source Installation

```bash
rm -rf ~/phronesis
```

### Docker

```bash
docker rmi hyperpolymath/phronesis
```

---

## Next Steps

- [Quick Start](Quick-Start.md) - Write your first policy
- [CLI Reference](CLI-Reference.md) - Learn the command line
- [REPL Guide](REPL-Guide.md) - Interactive exploration

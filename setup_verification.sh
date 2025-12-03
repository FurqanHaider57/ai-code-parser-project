#!/bin/bash
# Setup script for Formal Verification dependencies

echo "🚀 Setting up Formal Verification environment..."

# Install Python dependencies
echo "📦 Installing Python packages..."
pip install openai anthropic tree-sitter

# Optional: Install Frama-C (Ubuntu/Debian)
echo "🔧 Installing Frama-C (optional)..."
# sudo apt-get update
# sudo apt-get install frama-c

echo "✅ Setup complete!"
echo "Note: You may need to manually install Frama-C for full verification support"

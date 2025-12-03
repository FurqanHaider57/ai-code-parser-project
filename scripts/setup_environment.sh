#!/bin/bash
echo "Setting up AI Code Parser development environment"

# Create .env file for API keys
cat > .env << 'ENVFILE'
# AI API Keys (replace with your actual keys)
OPENAI_API_KEY=your_openai_key_here
ANTHROPIC_API_KEY=your_anthropic_key_here

# Development settings
PYTHONPATH=$(pwd)
LOG_LEVEL=INFO
ENVFILE

echo "Environment file created (.env)"
echo "Please update API keys in .env file before running the application"

# Install VS Code extensions if VS Code is available
if command -v code &> /dev/null; then
    echo "Installing VS Code extensions..."
    code --install-extension ms-python.python
    code --install-extension ms-vscode.cpptools
    code --install-extension github.copilot
    code --install-extension ms-python.black-formatter
    echo "VS Code extensions installed"
fi

echo "Environment setup complete!"

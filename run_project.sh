#!/bin/bash
# ============================================
# AI Code Parser - WSL Launcher Script (Fully Hands-Free)
# ============================================

# Function: Ensure .env has correct keys and models
update_env_file() {
    ENV_FILE=".env"
    
    echo "🔧 Updating .env for local Ollama usage..."
    [ ! -f "$ENV_FILE" ] && touch "$ENV_FILE"

    # Remove old entries
    sed -i '/^OPENAI_API_KEY=/d' "$ENV_FILE"
    sed -i '/^ANTHROPIC_API_KEY=/d' "$ENV_FILE"
    sed -i '/^DEFAULT_LLM_MODEL=/d' "$ENV_FILE"
    sed -i '/^BACKUP_LLM_MODEL=/d' "$ENV_FILE"

    # Add correct entries
    echo "OPENAI_API_KEY=ollama" >> "$ENV_FILE"
    echo "ANTHROPIC_API_KEY=ollama" >> "$ENV_FILE"
    echo "DEFAULT_LLM_MODEL=llama3" >> "$ENV_FILE"
    echo "BACKUP_LLM_MODEL=mistral" >> "$ENV_FILE"

    echo "✅ .env updated successfully"
}

# Function: Check if Ollama is running
is_ollama_running() {
    pgrep -f "ollama serve" > /dev/null 2>&1
}

# Function: Check if a model is installed
is_model_installed() {
    local model=$1
    ollama list models | grep -q "$model"
}

# Function: Install a model if not installed
install_model() {
    local model=$1
    if ! is_model_installed "$model"; then
        echo "📥 Installing Ollama model: $model ..."
        ollama pull "$model"
        echo "✅ Model $model installed"
    else
        echo "✅ Model $model already installed"
    fi
}

# Step 0: Update .env
update_env_file

# Step 1: Ensure Ollama server is running
if is_ollama_running; then
    echo "✅ Ollama server already running."
else
    echo "🚀 Starting Ollama server..."
    nohup ollama serve > ollama.log 2>&1 &
    sleep 5
fi

# Step 2: Ensure required models are installed
install_model "llama3"
install_model "mistral"

# Step 3: Activate Python virtual environment
echo "🐍 Activating Python virtual environment..."
source ./venv/bin/activate

# Step 4: Run main project
echo "📦 Running AI Code Parser..."
python main.py

echo "🎉 Done! Ollama server is still running for next run."


#pkill -f "ollama serve"

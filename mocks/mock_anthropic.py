# mocks/mock_anthropic.py
import os
from openai import OpenAI # type: ignore

class Client:
    def __init__(self, api_key=None, base_url=None):
        self.api_key = api_key or os.getenv("ANTHROPIC_API_KEY", "ollama")
        self.base_url = base_url or os.getenv("OPENAI_API_BASE", "http://localhost:11434/v1")
        self.client = OpenAI(base_url=self.base_url, api_key=self.api_key)

    def messages(self, model=None, max_tokens=None, temperature=None, messages=None):
        """
        Mimics anthropic.Client().messages.create() using local Ollama.
        """
        resp = self.client.chat.completions.create(
            model=model or os.getenv("DEFAULT_LLM_MODEL", "llama3"),
            messages=messages or [],
            max_tokens=max_tokens or int(os.getenv("MAX_TOKENS", "1024")),
            temperature=temperature or float(os.getenv("TEMPERATURE", "0.1")),
        )
        return {
            "content": resp.choices[0].message["content"],
            "stop_reason": resp.choices[0].finish_reason
        }

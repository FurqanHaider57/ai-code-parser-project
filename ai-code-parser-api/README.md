# AI Code Parser API

## Overview
The AI Code Parser API is a Flask-based web application that integrates three distinct modules: debugging, NLP (Natural Language Processing), and formal verification. Each module is accessible through dedicated API endpoints, allowing users to interact with the functionalities provided by these modules.

## Project Structure
```
ai-code-parser-api/
├── app/                     # Application package
│   ├── __init__.py         # Initializes the Flask application
│   ├── routes/              # Contains route definitions
│   │   ├── __init__.py     # Initializes the routes module
│   │   ├── debugging.py     # Endpoint for debugging functionality
│   │   ├── nlp.py          # Endpoint for NLP functionality
│   │   └── formal.py       # Endpoint for formal verification functionality
│   ├── services/            # Contains service logic for each module
│   │   ├── __init__.py     # Initializes the services module
│   │   ├── debugger_service.py # Logic for debugging module
│   │   ├── nlp_service.py   # Logic for NLP module
│   │   └── formal_service.py # Logic for formal verification module
│   ├── models/              # Contains data models and schemas
│   │   ├── __init__.py     # Initializes the models module
│   │   └── schemas.py      # Data schemas for validation and serialization
│   └── utils/               # Utility functions
│       ├── __init__.py     # Initializes the utils module
│       └── response_formatter.py # Functions for formatting API responses
├── config/                  # Configuration settings
│   ├── __init__.py         # Initializes the configuration module
│   └── settings.py         # Application settings
├── tests/                   # Unit tests for the application
│   ├── __init__.py         # Initializes the tests module
│   ├── test_debugging.py    # Tests for debugging API
│   ├── test_nlp.py         # Tests for NLP API
│   └── test_formal.py      # Tests for formal verification API
├── app.py                   # Entry point of the application
├── requirements.txt         # Project dependencies
├── .env.example             # Example environment variables
└── README.md                # Project documentation
```

## Setup Instructions
1. **Clone the Repository**
   ```
   git clone <repository-url>
   cd ai-code-parser-api
   ```

2. **Create a Virtual Environment**
   ```
   python -m venv venv
   ```

3. **Activate the Virtual Environment**
   - On Windows:
     ```
     venv\Scripts\activate
     ```
   - On macOS/Linux:
     ```
     source venv/bin/activate
     ```

4. **Install Dependencies**
   ```
   pip install -r requirements.txt
   ```

5. **Run the Application**
   ```
   python app.py
   ```

## Usage
- **Debugging Endpoint**: Access the debugging functionality at `/api/debugging`.
- **NLP Endpoint**: Access the NLP functionality at `/api/nlp`.
- **Formal Verification Endpoint**: Access the formal verification functionality at `/api/formal`.

## Contributing
Contributions are welcome! Please submit a pull request or open an issue for any enhancements or bug fixes.

## License
This project is licensed under the MIT License. See the LICENSE file for details.
# modules/__init__.py
# This file makes it easy to import all main classes from one place

# Module 1: Debugging
from .module1_debugging import AIDebugger

# Module 2: NLP
from .module2_nlp.nlp_test_generator import NLPTestGenerator

# Module 3: Formal Verification
from .module3_formal.formal_verifier import FormalVerifier

# Module 4: Simulink
from .module4_simulink.simulink_generator import SimulinkGenerator

__all__ = [
    "AIDebugger",
    "NLPTestGenerator",
    "FormalVerifier",
    "SimulinkGenerator"
]

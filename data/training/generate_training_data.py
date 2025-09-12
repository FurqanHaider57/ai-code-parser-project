"""
Generate training data for NLP test case generation
"""
import json
import random
from pathlib import Path

# Sample specifications and corresponding test cases for training
TRAINING_EXAMPLES = [
    {
        "specification": "Function should calculate factorial of positive integers and return error for negative inputs",
        "test_cases": [
            "Test with positive integer: factorial(5) should return 120",
            "Test with zero: factorial(0) should return 1", 
            "Test with negative integer: factorial(-1) should return error",
            "Test with large number: factorial(10) should return 3628800",
            "Boundary test: factorial(1) should return 1"
        ],
        "function_signature": "int factorial(int n)",
        "domain": "mathematical"
    },
    {
        "specification": "PID controller function takes setpoint, measurement, and PID gains, returns control output",
        "test_cases": [
            "Test normal operation: pid_control(100, 95, 0.1, 0.01, 0.05) should return positive correction",
            "Test at setpoint: pid_control(100, 100, 0.1, 0.01, 0.05) should return small output",
            "Test overshoot: pid_control(100, 105, 0.1, 0.01, 0.05) should return negative correction",
            "Test zero gains: pid_control(100, 95, 0, 0, 0) should return zero",
            "Test stability: pid_control with constant inputs should converge"
        ],
        "function_signature": "float pid_control(float setpoint, float measurement, float kp, float ki, float kd)",
        "domain": "control_systems"
    },
    {
        "specification": "Digital filter function processes input signal and returns filtered output with specified frequency response",
        "test_cases": [
            "Test DC input: filter with constant input should pass DC component",
            "Test frequency response: filter should attenuate high frequencies",
            "Test impulse response: single pulse input should show filter characteristics",
            "Test stability: filter output should remain bounded for bounded input",
            "Test initialization: filter should handle first sample correctly"
        ],
        "function_signature": "float digital_filter(float input, float coeffs[], int order)",
        "domain": "signal_processing"
    },
    {
        "specification": "Memory allocation function allocates requested bytes and returns pointer, handles out-of-memory conditions",
        "test_cases": [
            "Test normal allocation: allocate(1024) should return valid pointer",
            "Test zero allocation: allocate(0) behavior should be defined",
            "Test large allocation: allocate beyond available memory should handle gracefully", 
            "Test alignment: allocated memory should meet alignment requirements",
            "Test cleanup: allocated memory should be properly freed"
        ],
        "function_signature": "void* safe_malloc(size_t size)",
        "domain": "memory_management"
    }
]

def generate_training_dataset(output_dir: Path, num_augmented: int = 1000):
    """Generate augmented training dataset"""
    
    output_dir = Path(output_dir)
    output_dir.mkdir(parents=True, exist_ok=True)
    
    # Base examples
    dataset = TRAINING_EXAMPLES.copy()
    
    # Generate augmented examples
    for _ in range(num_augmented):
        base_example = random.choice(TRAINING_EXAMPLES)
        
        # Create variations
        augmented = create_augmented_example(base_example)
        dataset.append(augmented)
    
    # Split into train/validation
    random.shuffle(dataset)
    train_size = int(0.8 * len(dataset))
    
    train_set = dataset[:train_size]
    val_set = dataset[train_size:]
    
    # Save datasets
    with open(output_dir / "train_data.json", "w") as f:
        json.dump(train_set, f, indent=2)
    
    with open(output_dir / "validation_data.json", "w") as f:
        json.dump(val_set, f, indent=2)
    
    print(f"✅ Generated {len(train_set)} training examples")
    print(f"✅ Generated {len(val_set)} validation examples")
    
    return len(dataset)

def create_augmented_example(base_example):
    """Create augmented version of base example"""
    
    domains = ["mathematical", "control_systems", "signal_processing", "memory_management", "networking", "file_io"]
    
    # Template variations
    spec_templates = [
        "Function must {action} and {requirement}",
        "The {function_type} should {behavior} when {condition}",
        "Implementation needs to {primary_action} while {constraint}",
        "{function_name} shall {specification} according to {standard}"
    ]
    
    test_templates = [
        "Verify {behavior} when {input_condition}",
        "Test {scenario}: {expected_outcome}",
        "Validate {aspect} under {test_condition}",
        "Check {property} with {test_data}"
    ]
    
    # Generate new example
    augmented = {
        "specification": random.choice(spec_templates).format(
            action="process input data",
            requirement="handle edge cases",
            function_type="algorithm", 
            behavior="return correct results",
            condition="given valid parameters",
            primary_action="compute values",
            constraint="maintaining performance",
            function_name="process_function",
            specification="perform its intended function", 
            standard="requirements"
        ),
        "test_cases": [
            random.choice(test_templates).format(
                behavior="correct output",
                input_condition="valid input",
                scenario="Normal operation",
                expected_outcome="function returns expected result",
                aspect="input validation", 
                test_condition="boundary conditions",
                property="output correctness",
                test_data="sample inputs"
            ) for _ in range(random.randint(3, 6))
        ],
        "function_signature": generate_function_signature(),
        "domain": random.choice(domains)
    }
    
    return augmented

def generate_function_signature():
    """Generate random function signature"""
    return_types = ["int", "float", "double", "void*", "bool", "char*"]
    param_types = ["int", "float", "double", "char*", "void*", "bool"]
    
    return_type = random.choice(return_types)
    num_params = random.randint(1, 4)
    
    params = []
    for i in range(num_params):
        param_type = random.choice(param_types)
        param_name = f"param{i+1}"
        params.append(f"{param_type} {param_name}")
    
    return f"{return_type} function_name({', '.join(params)})"

if __name__ == "__main__":
    generate_training_dataset("data/training", 500)
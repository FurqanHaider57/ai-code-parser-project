import re
import json
import os
import matplotlib.pyplot as plt
import matplotlib.patches as patches
from matplotlib.patches import FancyBboxPatch, ConnectionPatch
from typing import List, Dict, Tuple, Any
from dataclasses import dataclass, field
from enum import Enum

class BlockType(Enum):
    CONSTANT = "Constant"
    ADD = "Add"
    SUBTRACT = "Subtract"
    PRODUCT = "Product"
    DIVIDE = "Divide"
    DATA_STORE_MEMORY = "DataStoreMemory"
    DATA_STORE_READ = "DataStoreRead"
    DATA_STORE_WRITE = "DataStoreWrite"
    GAIN = "Gain"
    SQRT = "Sqrt"

@dataclass
class SimulinkBlock:
    block_id: str
    block_type: BlockType
    name: str
    parameters: Dict[str, Any] = field(default_factory=dict)
    position: Tuple[int, int, int, int] = (0, 0, 100, 50)
    inputs: List[str] = field(default_factory=list)
    outputs: List[str] = field(default_factory=list)

@dataclass
class Connection:
    source_block: str
    source_port: int
    dest_block: str
    dest_port: int

class ImprovedCFileToSimulinkConverter:
    def __init__(self):
        self.blocks: List[SimulinkBlock] = []
        self.connections: List[Connection] = []
        self.variables: Dict[str, str] = {}
        self.constants: Dict[str, str] = {}
        self.block_counter = 0
        self.position_x = 50
        self.position_y = 50
        self.current_function = ""
        self.intermediate_results = {}
        
    def reset(self):
        """Reset converter for new function"""
        self.blocks.clear()
        self.connections.clear()
        self.variables.clear()
        self.constants.clear()
        self.block_counter = 0
        self.position_x = 50
        self.position_y = 50
        self.intermediate_results.clear()
        
    def get_next_block_id(self) -> str:
        self.block_counter += 1
        return f"Block_{self.block_counter}"
    
    def get_next_position(self, width=120, height=60) -> Tuple[int, int, int, int]:
        pos = (self.position_x, self.position_y, self.position_x + width, self.position_y + height)
        self.position_x += width + 80
        if self.position_x > 1200:
            self.position_x = 50
            self.position_y += 100
        return pos
    
    def read_c_file(self, filename: str) -> Dict[str, str]:
        """Read C file and extract functions with their code"""
        try:
            with open(filename, 'r', encoding='utf-8') as file:
                content = file.read()
        except FileNotFoundError:
            print(f"Error: File '{filename}' not found!")
            return {}
        except Exception as e:
            print(f"Error reading file: {e}")
            return {}
        
        # Remove comments
        content = re.sub(r'/\*.*?\*/', '', content, flags=re.DOTALL)
        content = re.sub(r'//.*$', '', content, flags=re.MULTILINE)
        
        # Extract functions
        functions = {}
        function_pattern = r'void\s+(\w+)\s*\([^)]*\)\s*\{([^}]*(?:\{[^}]*\}[^}]*)*)\}'
        
        matches = re.finditer(function_pattern, content, re.DOTALL)
        
        for match in matches:
            func_name = match.group(1)
            func_body = match.group(2).strip()
            
            # Extract only assignment statements
            lines = func_body.split('\n')
            assignment_lines = []
            
            for line in lines:
                line = line.strip()
                if line and any(op in line for op in ['+=', '-=', '*=', '/=', '=']):
                    # Skip declarations and comparisons
                    if not line.startswith(('int ', 'float ', 'double ', 'char ')) and \
                       not any(comp in line for comp in ['==', '!=', '<=', '>=', '<', '>']):
                        assignment_lines.append(line)
            
            if assignment_lines:
                functions[func_name] = '\n'.join(assignment_lines)
        
        return functions
    
    def create_constant_block(self, value: str) -> str:
        if value in self.constants:
            return self.constants[value]
        
        block_id = self.get_next_block_id()
        block = SimulinkBlock(
            block_id=block_id,
            block_type=BlockType.CONSTANT,
            name=f"Const_{value}",
            parameters={"Value": value},
            position=self.get_next_position(80, 50),
            outputs=[f"{block_id}_out"]
        )
        self.blocks.append(block)
        self.constants[value] = block_id
        return block_id
    
    def create_variable_blocks(self, var_name: str, initial_value: str = "0") -> str:
        if var_name in self.variables:
            return self.variables[var_name]
        
        memory_block_id = self.get_next_block_id()
        memory_block = SimulinkBlock(
            block_id=memory_block_id,
            block_type=BlockType.DATA_STORE_MEMORY,
            name=f"DSM_{var_name}",
            parameters={"DataStoreName": var_name, "InitialValue": initial_value},
            position=self.get_next_position(100, 50)
        )
        self.blocks.append(memory_block)
        self.variables[var_name] = memory_block_id
        return memory_block_id
    
    def create_data_store_read(self, var_name: str, initial_value: str = "0") -> str:
        self.create_variable_blocks(var_name, initial_value)
        
        block_id = self.get_next_block_id()
        block = SimulinkBlock(
            block_id=block_id,
            block_type=BlockType.DATA_STORE_READ,
            name=f"Read_{var_name}",
            parameters={"DataStoreName": var_name},
            position=self.get_next_position(100, 50),
            outputs=[f"{block_id}_out"]
        )
        self.blocks.append(block)
        return block_id
    
    def create_data_store_write(self, var_name: str, input_block_id: str, initial_value: str = "0") -> str:
        self.create_variable_blocks(var_name, initial_value)
        
        block_id = self.get_next_block_id()
        block = SimulinkBlock(
            block_id=block_id,
            block_type=BlockType.DATA_STORE_WRITE,
            name=f"Write_{var_name}",
            parameters={"DataStoreName": var_name},
            position=self.get_next_position(100, 50),
            inputs=[f"{block_id}_in"]
        )
        self.blocks.append(block)
        
        self.connections.append(Connection(
            source_block=input_block_id,
            source_port=0,
            dest_block=block_id,
            dest_port=0
        ))
        return block_id
    
    def create_math_block(self, operation: str, operands: List[str], custom_name: str = None) -> str:
        block_id = self.get_next_block_id()
        
        op_map = {
            '+': (BlockType.ADD, "Add"),
            '-': (BlockType.SUBTRACT, "Subtract"),
            '*': (BlockType.PRODUCT, "Product"),
            '/': (BlockType.DIVIDE, "Divide")
        }
        
        if operation not in op_map:
            raise ValueError(f"Unsupported operation: {operation}")
        
        block_type, base_name = op_map[operation]
        block_name = custom_name if custom_name else f"{base_name}_{block_id}"
        
        # Set appropriate inputs parameter for Add/Subtract blocks
        inputs_param = {}
        if operation == '+':
            inputs_param['Inputs'] = '+' * len(operands)
        elif operation == '-':
            inputs_param['Inputs'] = '+' + '-' * (len(operands) - 1)
        
        block = SimulinkBlock(
            block_id=block_id,
            block_type=block_type,
            name=block_name,
            parameters=inputs_param,
            position=self.get_next_position(80, 60),
            inputs=[f"{block_id}_in{i}" for i in range(len(operands))],
            outputs=[f"{block_id}_out"]
        )
        self.blocks.append(block)
        
        for i, operand_block in enumerate(operands):
            self.connections.append(Connection(
                source_block=operand_block,
                source_port=0,
                dest_block=block_id,
                dest_port=i
            ))
        
        return block_id
    
    def parse_expression(self, expr: str) -> str:
        expr = expr.strip()
        
        # Handle parentheses first
        while '(' in expr:
            start = -1
            for i, char in enumerate(expr):
                if char == '(':
                    start = i
                elif char == ')' and start != -1:
                    inner_expr = expr[start+1:i]
                    result_block = self.parse_expression(inner_expr)
                    placeholder = f"BLOCK_{result_block}"
                    expr = expr[:start] + placeholder + expr[i+1:]
                    break
        
        # Handle multiplication and division (higher precedence)
        expr = self.handle_high_precedence_ops(expr)
        
        # Handle addition and subtraction (lower precedence)
        expr = self.handle_low_precedence_ops(expr)
        
        if expr.startswith("BLOCK_"):
            return expr.replace("BLOCK_", "")
        
        return self.create_operand_block(expr)
    
    def handle_high_precedence_ops(self, expr: str) -> str:
        while '*' in expr or '/' in expr:
            mul_pos = expr.find('*')
            div_pos = expr.find('/')
            
            if mul_pos == -1:
                op_pos = div_pos
                op = '/'
            elif div_pos == -1:
                op_pos = mul_pos
                op = '*'
            else:
                op_pos = min(mul_pos, div_pos)
                op = expr[op_pos]
            
            left_operand = self.extract_left_operand(expr, op_pos)
            right_operand = self.extract_right_operand(expr, op_pos + 1)
            
            left_block = self.create_operand_block(left_operand)
            right_block = self.create_operand_block(right_operand)
            
            result_block = self.create_math_block(op, [left_block, right_block])
            
            start_pos = op_pos - len(left_operand)
            end_pos = op_pos + 1 + len(right_operand)
            expr = expr[:start_pos] + f"BLOCK_{result_block}" + expr[end_pos:]
        
        return expr
    
    def handle_low_precedence_ops(self, expr: str) -> str:
        while '+' in expr or '-' in expr:
            add_pos = expr.find('+')
            sub_pos = expr.find('-')
            
            # Skip leading negative sign
            if sub_pos == 0:
                sub_pos = expr.find('-', 1)
            
            if add_pos == -1:
                op_pos = sub_pos
                op = '-'
            elif sub_pos == -1:
                op_pos = add_pos
                op = '+'
            else:
                op_pos = min(add_pos, sub_pos)
                op = expr[op_pos]
            
            if op_pos == -1:
                break
            
            left_operand = self.extract_left_operand(expr, op_pos)
            right_operand = self.extract_right_operand(expr, op_pos + 1)
            
            left_block = self.create_operand_block(left_operand)
            right_block = self.create_operand_block(right_operand)
            
            result_block = self.create_math_block(op, [left_block, right_block])
            
            start_pos = op_pos - len(left_operand)
            end_pos = op_pos + 1 + len(right_operand)
            expr = expr[:start_pos] + f"BLOCK_{result_block}" + expr[end_pos:]
        
        return expr
    
    def extract_left_operand(self, expr: str, op_pos: int) -> str:
        start = op_pos - 1
        while start >= 0:
            if expr[start] in '+-*/':
                start += 1
                break
            start -= 1
        if start < 0:
            start = 0
        return expr[start:op_pos].strip()
    
    def extract_right_operand(self, expr: str, start_pos: int) -> str:
        end = start_pos
        while end < len(expr):
            if expr[end] in '+-*/':
                break
            end += 1
        return expr[start_pos:end].strip()
    
    def create_operand_block(self, operand: str) -> str:
        operand = operand.strip()
        
        if operand.startswith("BLOCK_"):
            return operand.replace("BLOCK_", "")
        
        # Check if it's a number
        try:
            float(operand)
            return self.create_constant_block(operand)
        except ValueError:
            pass
        
        # Get appropriate initial values for common variables
        initial_values = {
            'a': '1', 'b': '2', 'c': '3',
            'gain1': '2', 'gain2': '3', 'input': '10',
            'myConst1': '5', 'myConst2': '2', 'myConst3': '3', 'myConst4': '1',
            'offset': '1', 'scale_factor': '1.5'
        }
        initial_value = initial_values.get(operand, '0')
        
        return self.create_data_store_read(operand, initial_value)
    
    def parse_assignment(self, statement: str) -> None:
        statement = statement.strip().rstrip(';')
        
        if '+=' in statement:
            var_name, expr = statement.split('+=', 1)
            var_name = var_name.strip()
            expr = expr.strip()
            
            current_var_block = self.create_data_store_read(var_name)
            expr_result_block = self.parse_expression(expr)
            add_block = self.create_math_block('+', [current_var_block, expr_result_block])
            self.create_data_store_write(var_name, add_block)
            
        elif '-=' in statement:
            var_name, expr = statement.split('-=', 1)
            var_name = var_name.strip()
            expr = expr.strip()
            
            current_var_block = self.create_data_store_read(var_name)
            expr_result_block = self.parse_expression(expr)
            sub_block = self.create_math_block('-', [current_var_block, expr_result_block])
            self.create_data_store_write(var_name, sub_block)
            
        elif '*=' in statement:
            var_name, expr = statement.split('*=', 1)
            var_name = var_name.strip()
            expr = expr.strip()
            
            current_var_block = self.create_data_store_read(var_name)
            expr_result_block = self.parse_expression(expr)
            mul_block = self.create_math_block('*', [current_var_block, expr_result_block])
            self.create_data_store_write(var_name, mul_block)
            
        elif '/=' in statement:
            var_name, expr = statement.split('/=', 1)
            var_name = var_name.strip()
            expr = expr.strip()
            
            current_var_block = self.create_data_store_read(var_name)
            expr_result_block = self.parse_expression(expr)
            div_block = self.create_math_block('/', [current_var_block, expr_result_block])
            self.create_data_store_write(var_name, div_block)
            
        elif '=' in statement and not any(op in statement for op in ['==', '!=', '<=', '>=']):
            var_name, expr = statement.split('=', 1)
            var_name = var_name.strip()
            expr = expr.strip()
            
            expr_result_block = self.parse_expression(expr)
            self.create_data_store_write(var_name, expr_result_block)
    
    def convert_c_code(self, c_code: str) -> None:
        lines = c_code.strip().split('\n')
        
        for line in lines:
            line = line.strip()
            
            if not line or line.startswith('//') or line.startswith('/*'):
                continue
            
            line = re.sub(r'//.*', '', line)
            line = re.sub(r'/\*.*?\*/', '', line)
            line = line.strip()
            
            if not line:
                continue
            
            if any(op in line for op in ['+=', '-=', '*=', '/=', '=']):
                self.parse_assignment(line)
    
    def generate_matlab_script(self, model_name: str = "GeneratedModel") -> str:
        script = f"""% Auto-generated MATLAB script for Simulink model creation
% Model: {model_name}
% Function: {self.current_function}

function create_{model_name.lower().replace('model_', '')}()
    % Load Simulink library
    load_system('simulink');
    
    % Create new model
    model_name = '{model_name}';
    
    % Check if model already exists and close it
    if bdIsLoaded(model_name)
        close_system(model_name, 0);
    end
    
    % Create new system
    new_system(model_name);
    open_system(model_name);
    
    try
"""
        
        # Group blocks by type for better organization
        memory_blocks = [b for b in self.blocks if b.block_type == BlockType.DATA_STORE_MEMORY]
        read_blocks = [b for b in self.blocks if b.block_type == BlockType.DATA_STORE_READ]
        write_blocks = [b for b in self.blocks if b.block_type == BlockType.DATA_STORE_WRITE]
        math_blocks = [b for b in self.blocks if b.block_type in [BlockType.ADD, BlockType.SUBTRACT, BlockType.PRODUCT, BlockType.DIVIDE]]
        const_blocks = [b for b in self.blocks if b.block_type == BlockType.CONSTANT]
        
        # Add Data Store Memory blocks first
        if memory_blocks:
            script += "        % Data Store Memory blocks\n"
            for block in memory_blocks:
                x1, y1, x2, y2 = block.position
                script += f"        add_block('simulink/Signal Routing/Data Store Memory', [model_name '/{block.name}'], ...\n"
                script += f"            'Position', [{x1}, {y1}, {x2}, {y2}]"
                
                for param, value in block.parameters.items():
                    if isinstance(value, str):
                        script += f", ...\n            '{param}', '{value}'"
                    else:
                        script += f", ...\n            '{param}', {value}"
                
                script += ");\n\n"
        
        # Add Constant blocks
        if const_blocks:
            script += "        % Constant blocks\n"
            for block in const_blocks:
                x1, y1, x2, y2 = block.position
                script += f"        add_block('simulink/Sources/Constant', [model_name '/{block.name}'], ...\n"
                script += f"            'Position', [{x1}, {y1}, {x2}, {y2}]"
                
                for param, value in block.parameters.items():
                    if isinstance(value, str):
                        script += f", ...\n            '{param}', '{value}'"
                    else:
                        script += f", ...\n            '{param}', {value}"
                
                script += ");\n\n"
        
        # Add Data Store Read blocks
        if read_blocks:
            script += "        % Data Store Read blocks\n"
            for block in read_blocks:
                x1, y1, x2, y2 = block.position
                script += f"        add_block('simulink/Signal Routing/Data Store Read', [model_name '/{block.name}'], ...\n"
                script += f"            'Position', [{x1}, {y1}, {x2}, {y2}]"
                
                for param, value in block.parameters.items():
                    if isinstance(value, str):
                        script += f", ...\n            '{param}', '{value}'"
                    else:
                        script += f", ...\n            '{param}', {value}"
                
                script += ");\n\n"
        
        # Add Math Operation blocks
        if math_blocks:
            script += "        % Math Operation blocks\n"
            for block in math_blocks:
                x1, y1, x2, y2 = block.position
                
                if block.block_type == BlockType.ADD:
                    lib_path = "simulink/Math Operations/Add"
                elif block.block_type == BlockType.SUBTRACT:
                    lib_path = "simulink/Math Operations/Add"  # Subtract uses Add block with +- inputs
                elif block.block_type == BlockType.PRODUCT:
                    lib_path = "simulink/Math Operations/Product"
                elif block.block_type == BlockType.DIVIDE:
                    lib_path = "simulink/Math Operations/Divide"
                
                script += f"        add_block('{lib_path}', [model_name '/{block.name}'], ...\n"
                script += f"            'Position', [{x1}, {y1}, {x2}, {y2}]"
                
                for param, value in block.parameters.items():
                    if isinstance(value, str):
                        script += f", ...\n            '{param}', '{value}'"
                    else:
                        script += f", ...\n            '{param}', {value}"
                
                script += ");\n\n"
        
        # Add Data Store Write blocks
        if write_blocks:
            script += "        % Data Store Write blocks\n"
            for block in write_blocks:
                x1, y1, x2, y2 = block.position
                script += f"        add_block('simulink/Signal Routing/Data Store Write', [model_name '/{block.name}'], ...\n"
                script += f"            'Position', [{x1}, {y1}, {x2}, {y2}]"
                
                for param, value in block.parameters.items():
                    if isinstance(value, str):
                        script += f", ...\n            '{param}', '{value}'"
                    else:
                        script += f", ...\n            '{param}', {value}"
                
                script += ");\n\n"
        
        # Add connections
        if self.connections:
            script += "        % Add connections\n"
            for conn in self.connections:
                source_block = next((b for b in self.blocks if b.block_id == conn.source_block), None)
                dest_block = next((b for b in self.blocks if b.block_id == conn.dest_block), None)
                
                if source_block and dest_block:
                    script += f"        add_line(model_name, '{source_block.name}/{conn.source_port + 1}', '{dest_block.name}/{conn.dest_port + 1}');\n"
        
        script += f"""
        % Save the model
        save_system(model_name);
        
        fprintf('Simulink model "%s" created successfully!\\n', model_name);
        
    catch ME
        fprintf('Error creating model: %s\\n', ME.message);
        if bdIsLoaded(model_name)
            close_system(model_name, 0);
        end
        rethrow(ME);
    end
end
"""
        return script
    
    def draw_simulink_diagram(self, title: str = "Simulink Block Diagram", save_path: str = None):
        if not self.blocks:
            print("No blocks to draw!")
            return
        
        fig, ax = plt.subplots(1, 1, figsize=(18, 12))
        ax.set_xlim(0, 1600)
        ax.set_ylim(0, 1000)
        ax.set_title(title, fontsize=16, fontweight='bold', pad=20)
        
        colors = {
            BlockType.CONSTANT: '#FFE6CC',
            BlockType.ADD: '#D4E6F1',
            BlockType.SUBTRACT: '#FADBD8',
            BlockType.PRODUCT: '#D5F4E6',
            BlockType.DIVIDE: '#F8D7DA',
            BlockType.DATA_STORE_MEMORY: '#E8DAEF',
            BlockType.DATA_STORE_READ: '#D1F2EB',
            BlockType.DATA_STORE_WRITE: '#FCF3CF',
            BlockType.SQRT: '#F0E68C'
        }
        
        block_positions = {}
        
        # Draw blocks
        for block in self.blocks:
            x1, y1, x2, y2 = block.position
            width = x2 - x1
            height = y2 - y1
            
            center_x = x1 + width/2
            center_y = y1 + height/2
            block_positions[block.block_id] = (center_x, center_y, x1, y1, x2, y2)
            
            rect = FancyBboxPatch(
                (x1, y1), width, height,
                boxstyle="round,pad=5",
                facecolor=colors.get(block.block_type, '#F0F0F0'),
                edgecolor='black',
                linewidth=2
            )
            ax.add_patch(rect)
            
            # Block name
            ax.text(center_x, center_y + 8, block.name, 
                   ha='center', va='center', fontsize=9, fontweight='bold')
            
            # Block type
            ax.text(center_x, center_y - 5, block.block_type.value, 
                   ha='center', va='center', fontsize=7, style='italic')
            
            # Parameters
            if block.block_type == BlockType.CONSTANT and 'Value' in block.parameters:
                ax.text(center_x, center_y - 18, f"Val: {block.parameters['Value']}", 
                       ha='center', va='center', fontsize=6)
        
        # Draw connections
        for conn in self.connections:
            if (conn.source_block in block_positions and 
                conn.dest_block in block_positions):
                
                src_pos = block_positions[conn.source_block]
                dest_pos = block_positions[conn.dest_block]
                
                src_x = src_pos[4]  # Right edge
                src_y = src_pos[1] + (src_pos[5] - src_pos[3])/2  # Middle height
                dest_x = dest_pos[2]  # Left edge
                dest_y = dest_pos[1] + (dest_pos[5] - dest_pos[3])/2  # Middle height
                
                # Draw connection line with arrow
                ax.annotate('', xy=(dest_x, dest_y), xytext=(src_x, src_y),
                           arrowprops=dict(arrowstyle='->', lw=2, color='blue'))
        
        ax.set_xlabel('X Position', fontsize=12)
        ax.set_ylabel('Y Position', fontsize=12)
        ax.grid(True, alpha=0.3)
        ax.invert_yaxis()  # Invert Y axis to match Simulink convention
        
        plt.tight_layout()
        
        if save_path:
            plt.savefig(save_path, dpi=300, bbox_inches='tight')
            print(f"Diagram saved to: {save_path}")
        
        plt.show()
    
    def print_summary(self):
        print(f"Generated {len(self.blocks)} blocks and {len(self.connections)} connections")
        print(f"Variables: {list(self.variables.keys())}")
        print(f"Constants: {list(self.constants.keys())}")


def create_sample_c_file():
    """Create a sample C file for testing"""
    c_content = '''/*
 * Sample C Code for Simulink Conversion
 * File: sample_code.c
 */

#include <stdio.h>
#include <math.h>

// Function 1: Basic arithmetic operations
void basic_operations() {
    int a=5,b=10;
    result = a + b;
    myVar += myConst1 - myConst2 * myConst3;
    myVar -= myConst4;
    output = (gain1 + gain2) * input - offset;
    output *= scale_factor;
}

// Function 2: PID Controller
void pid_controller() {
    error = setpoint - feedback;
    integral += error * dt;
    derivative = (error - prev_error) / dt;
    output = kp * error + ki * integral + kd * derivative;
    prev_error = error;
}

int main() {
    printf("Sample C code for conversion\\n");
    return 0;
}
'''
    
    with open('sample_code.c', 'w') as f:
        f.write(c_content)
    print("Created sample_code.c file")


def main():
    """Main function to demonstrate the complete workflow"""
    print("C FILE TO SIMULINK BLOCK CONVERTER")
    print("="*60)
    
    # Create sample C file
    print("Step 1: Creating sample C file...")
    create_sample_c_file()
    
    # Read and parse C file
    print("\nStep 2: Reading C file...")
    converter = ImprovedCFileToSimulinkConverter()
    
    filename = 'sample_code.c'
    if not os.path.exists(filename):
        print(f"Error: {filename} not found!")
        return
    
    functions = converter.read_c_file(filename)
    
    if not functions:
        print("No functions found in C file!")
        return
    
    print(f"Found {len(functions)} functions:")
    for func_name in functions.keys():
        print(f"   - {func_name}")
    
    # Convert each function
    print(f"\nStep 3: Converting functions to Simulink blocks...")
    
    results = {}
    
    for func_name, func_code in functions.items():
        print(f"\n{'='*50}")
        print(f"CONVERTING FUNCTION: {func_name}")
        print(f"{'='*50}")
        print("C Code:")
        print(func_code)
        print()
        
        # Reset converter for new function
        converter.reset()
        converter.current_function = func_name
        
        # Convert the function
        converter.convert_c_code(func_code)
        
        # Print summary
        converter.print_summary()
        
        # Generate visual diagram
        print(f"\nGenerating Simulink diagram for {func_name}...")
        diagram_title = f"Simulink Model: {func_name}()"
        save_path = f"{func_name}_simulink_diagram.png"
        converter.draw_simulink_diagram(diagram_title, save_path)
        
        # Generate MATLAB script
        matlab_script = converter.generate_matlab_script(f"Model_{func_name}")
        
        # Save MATLAB script
        matlab_filename = f"{func_name}_matlab_script.m"
        with open(matlab_filename, 'w') as f:
            f.write(matlab_script)
        print(f"MATLAB script saved to: {matlab_filename}")
        
        # Store results
        results[func_name] = {
            'blocks': len(converter.blocks),
            'connections': len(converter.connections),
            'variables': list(converter.variables.keys()),
            'constants': list(converter.constants.keys())
        }
        
        print(f"Conversion complete for {func_name}")
    
    # Summary report
    print(f"\n{'='*60}")
    print("CONVERSION SUMMARY REPORT")
    print(f"{'='*60}")
    
    total_blocks = sum(result['blocks'] for result in results.values())
    total_connections = sum(result['connections'] for result in results.values())
    
    print(f"Processed file: {filename}")
    print(f"Functions converted: {len(results)}")
    print(f"Total blocks generated: {total_blocks}")
    print(f"Total connections created: {total_connections}")
    print()
    
    for func_name, result in results.items():
        print(f"Function: {func_name}")
        print(f"  - Blocks: {result['blocks']}")
        print(f"  - Connections: {result['connections']}")
        print(f"  - Variables: {result['variables']}")
        print(f"  - Constants: {result['constants']}")
        print()
    
    print("Generated Files:")
    for func_name in results.keys():
        print(f"  - {func_name}_simulink_diagram.png")
        print(f"  - {func_name}_matlab_script.m")
    
    print(f"\nConversion completed successfully!")


if __name__ == "__main__":
    main()
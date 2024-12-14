import os
import re

def extract_imports(file_path):
    with open(file_path, 'r') as file:
        content = file.read()
        imports = re.findall(r'import\s+([^\n]+)', content)
        has_sorry = 'sorry' in content or 'admit' in content
    return imports, has_sorry

def generate_mermaid_diagram(directory):
    mermaid_code = [
        "graph LR",
        "    classDef green fill:#90EE90,stroke:#333,stroke-width:2px;",
        "    classDef lightPurple fill:#E6E6FA,stroke:#333,stroke-width:2px;",
        "    classDef mathlib fill:#90EE90,stroke:#333,stroke-width:2px;",
        "    %%{init: {'flowchart': {'nodeSpacing': 30, 'rankSpacing': 30, 'curve': 'basis', 'wrappingWidth': 100}}}%%"
    ]
    
    green_nodes = []
    purple_nodes = []
    dependencies = {}

    for root, _, files in os.walk(directory):
        for file in files:
            if file.endswith('.lean'):
                file_path = os.path.join(root, file)
                file_name = os.path.splitext(file)[0]  # Get the filename without extension
                imports, has_sorry = extract_imports(file_path)
                
                dependencies[file_name] = []
                
                for imp in imports:
                    if imp == "Mathlib":
                        dependencies[file_name].append("Mathlib")
                    else:
                        imp_parts = imp.split('.')
                        imp_name = imp_parts[-1]
                        dependencies[file_name].append(imp_name)
                
                if has_sorry:
                    purple_nodes.append(file_name)
                else:
                    green_nodes.append(file_name)

    # Generate connections
    for node, deps in dependencies.items():
        for dep in deps:
            mermaid_code.append(f"    {dep} --> {node}")

    # Add class assignments
    if green_nodes:
        mermaid_code.append(f"    class {','.join(green_nodes)} green;")
    if purple_nodes:
        mermaid_code.append(f"    class {','.join(purple_nodes)} lightPurple;")

    # Ensure Mathlib is green
    mermaid_code.append("    class Mathlib mathlib;")

    return "\n".join(mermaid_code)

# Usage
directory = "Hybrid"
mermaid_diagram = generate_mermaid_diagram(directory)
print(mermaid_diagram)

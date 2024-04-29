# Read HumanEval dataset from jsonl file and extract the programs to python files

import json
import os
# import sys


def main():
    # if len(sys.argv) != 2:
    #     print('Usage: python humaneval.py <jsonl_file>')
    #     sys.exit(1)

    # jsonl_file = sys.argv[1]
    jsonl_file = os.path.join(os.path.dirname(__file__), 'HumanEval.jsonl')
    with open(jsonl_file, 'r') as f:
        for line in f:
            data = json.loads(line)
            code = data['prompt'] + data['canonical_solution']
            # code = code.replace('\n', '\n    ')
            # code = 'def f():\n    ' + code
            # code = code + '\n\nprint(f())'
            filename = f"{data['task_id']}_{data['entry_point']}.py"
            with open(filename, 'w') as f:
                f.write(code)


if __name__ == '__main__':
    main()

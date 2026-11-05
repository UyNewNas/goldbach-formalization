"""Check exact declared pins and the explicitly selected dependency state; never mutate."""
import argparse
import json
import sys
from pathlib import Path

sys.dont_write_bytecode = True

from verify_dependency_state import STATES, verify_dependency_state


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--expected-state", choices=STATES, default="original-clean")
    args = parser.parse_args()
    result = verify_dependency_state(Path(__file__).resolve().parents[3], args.expected_state)
    print(json.dumps(result, sort_keys=True))


if __name__ == "__main__":
    main()

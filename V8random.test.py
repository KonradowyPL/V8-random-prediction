import V8random
import subprocess


def runTest(numbers, start, end):
    sequence = numbers[start:end]
    remaining = numbers[end:]
    
    generator = V8random.solve(sequence)
    for number in remaining:
        if number != next(generator):
            return print("fail")
    return print("Succes")


if __name__ == "__main__":
    process = subprocess.Popen(
        ["node", "test.js"],
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        text=True  # Ensures output is in string format (Python 3.7+)
    )
    stdout, stderr = process.communicate()
    stdout = stdout[:-1]
    numbers = list(map(float, stdout.split("\n")))
    runTest(numbers, 12, 12+63)
    

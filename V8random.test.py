import V8random
import subprocess


def runTest(numbers, start, end):
    sequence = numbers[start:end]
    remaining = numbers[end:]

    generator = V8random.solve(sequence)
    for index, number in enumerate(remaining):
        generated = next(generator)
        if number != generated:
            print()
            print("Generator failed!")
            print("Window len:", end-start,
                  "Start Index:", start, "End Index", end)
            print("Fail index:",index)
            print("Expected:", number, "Got:", generated)
            if generated in remaining:
                print("Wrong number index:", remaining.index(generated))
            print()
            print(numbers)
            return


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
    runTest(numbers, 12, 12+62)
    runTest(numbers, 1, 65)
    runTest(numbers, 1, 64)



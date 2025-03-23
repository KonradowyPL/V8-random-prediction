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
            print("Fail index:", index)
            print("Expected:", number, "Got:", generated)
            if generated in sequence:
                print("Relative wrong number index:",
                      sequence.index(generated) - end)

            print()
            print(numbers)
            raise RuntimeError("Test failed!")


if __name__ == "__main__":
    process = subprocess.Popen(
        ["node", "test.js"],
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        text=True
    )
    stdout, stderr = process.communicate()
    stdout = stdout[:-1]
    numbers = list(map(float, stdout.split("\n")))

    # example tests
    runTest(numbers, 12, 12+63)
    runTest(numbers, 12, 65)
    runTest(numbers, 1, 65)
    runTest(numbers, 0, 64)
    runTest(numbers, 17, 100)
    runTest(numbers, 0, 129)
    runTest(numbers, 4, 128)
    runTest(numbers, 50, 50+65)
    runTest(numbers, 1, 255)

    # brute force all possible combinations
    for start in range(0, 60):
        for length in range(start//64 + 64, 196):
            print("Running:", start, length)
            runTest(numbers, start, start + length)

    print("All tests passed!")

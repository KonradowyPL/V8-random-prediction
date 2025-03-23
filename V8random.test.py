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
            if generated in remaining:
                print("Wrong number index:", remaining.index(generated))

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

    print("All tests passed!")

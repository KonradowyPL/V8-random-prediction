import struct
import z3

sequence = [0.15923871415005353, 0.04336549949372803, 0.3862752026091234, 0.44851280523543857, 0.08167302834747203, 0.03036753926269764, 0.1353841058556584, 0.13271951889208866, 0.6869980900346104, 0.3706273812710761, 0.608949472593058, 0.3728168729976238, 0.43903812251004704, 0.3983344188546407, 0.8591043718401656, 0.8897908171028812, 0.42324344278067105, 0.06889982437831299, 0.39584339814431746, 0.0910125243139508, 0.5678330526077262, 0.8936543924934519, 0.6072590271621732, 0.7312777957538501, 0.6880408005731018, 0.2941481174697993, 0.6092282983447941, 0.12420830850781517, 0.9116987499276916, 0.7722462653630251, 0.634633965156709, 0.0007998235285560096,
            0.8370330873961513, 0.7985800626273878, 0.8908451786957272, 0.6621872791526808, 0.6192890196160312, 0.07494320168145863, 0.9442681652090794, 0.3859832884541614, 0.6665405304346177, 0.5230977896216298, 0.22312153425755277, 0.1250135437430797, 0.9980529428557101, 0.7362621296111185, 0.18127601480945543, 0.5067832561607248, 0.6454331925776637, 0.7701774694394004, 0.7243234931888078, 0.0914305947387295, 0.5315761743687102, 0.4700802448896637, 0.18306027288642213, 0.5492917122690992, 0.05353387443639912, 0.2106803305312117, 0.07635881558073443, 0.8894654241584554, 0.39447316524739473, 0.7485857750690736, 0.6574026882090545, 0.11957860433247491]


# I have no idea how it works
# Function copppied from https://github.com/PwnFunction/v8-randomness-predictor/blob/main/main.py
def getStates(sequence) -> tuple[int, int]:
    sequence = sequence[::-1]
    solver = z3.Solver()
    se_state0, se_state1 = z3.BitVecs("se_state0 se_state1", 64)
    for i in range(len(sequence)):
        se_s1 = se_state0
        se_s0 = se_state1
        se_state0 = se_s0
        se_s1 ^= se_s1 << 23
        # Logical shift instead of Arthmetric shift
        se_s1 ^= z3.LShR(se_s1, 17)
        se_s1 ^= se_s0
        se_s1 ^= z3.LShR(se_s0, 26)
        se_state1 = se_s1
        float_64 = struct.pack("d", sequence[i] + 1)
        u_long_long_64 = struct.unpack("<Q", float_64)[0]
        mantissa = u_long_long_64 & ((1 << 52) - 1)
        solver.add(int(mantissa) == z3.LShR(se_state0, 12))
    if solver.check() == z3.sat:
        model = solver.model()
        states = {}
        for state in model.decls():
            states[state.__str__()] = model[state]
        state0 = states["se_state0"].as_long()
        state1 = states["se_state1"].as_long()

        return state0, state1
    raise RuntimeError("No solution found")


# Python rewrite of https://github.com/v8/v8/blob/3bfafd1f08b18ebb10cebc3ae59402f50df93d06/src/base/utils/random-number-generator.h#L121
def xorshift64(state0, state1) -> tuple[int, int]:
    MASK = 0xFFFFFFFFFFFFFFFF

    s1 = state0
    s0 = state1
    state0 = state1
    s1 ^= (s1 << 23) & MASK
    s1 ^= (s1 >> 17) & MASK
    s1 ^= s0 & MASK
    s1 ^= (s0 >> 26) & MASK
    state1 = s1
    return state0, state1


# Python rewrite of https://github.com/v8/v8/blob/3bfafd1f08b18ebb10cebc3ae59402f50df93d06/src/base/utils/random-number-generator.h#L111
def to_double(state0: int) -> float:
    u_long_long_64 = (state0 >> 12) | 0x3FF0000000000000
    float_64 = struct.pack("<Q", u_long_long_64)
    next_sequence = struct.unpack("d", float_64)[0]
    return next_sequence - 1  # Maps [1,2) to [0,1)


# generator, that returns next random numbers
def solve(sequence):
    sequence = sequence[:64]
    state0, state1 = getStates(sequence[0:5])

    # save current states for later
    states = (state0, state1)

    index = 0

    # run until array wraps
    while (to_double(state0) not in sequence) or index <= 5:
        index += 1
        state0, state1 = xorshift64(state0, state1)
        if index > len(sequence) + 64:
            raise RuntimeError("Sequence len to short. No results found")

    # find index where buffer edge is
    while to_double(state1) in sequence:
        state0, state1 = xorshift64(state0, state1)

    # calculate amount needed to get to the start of the buffer
    # addding 5 is because of getting first 5 elements to calculate state
    num = 64 - sequence.index(to_double(state0)) + 5
    state0, state1 = states

    # finally get to the start of the buffer
    for _ in range(num):
        state0, state1 = xorshift64(state0, state1)

    def refillCache():
        nonlocal state0
        nonlocal state1
        nonlocal cache

        cache = []
        for _ in range(64):
            state0, state1 = xorshift64(state0, state1)
            cache.append(to_double(state0))

    # prefill cache 
    cache = []
    cacheIndex = 64 - num + 5 - 1
    refillCache()

    while True:
        if cacheIndex < 0:
            refillCache()
            cacheIndex = 63
        # walk through cache in reverse order
        yield cache[cacheIndex]
        cacheIndex -= 1


if __name__ == "__main__":
    generator = solve(sequence)
    for i in range(128):
        print(i+1, next(generator))

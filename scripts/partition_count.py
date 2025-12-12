import math

def count_partitions(n: int) -> int:
    # Stirling numbers of the second kind S(n, k)
    S = [[0] * (n + 1) for _ in range(n + 1)]
    S[0][0] = 1

    for i in range(1, n + 1):
        for k in range(1, i + 1):
            S[i][k] = k * S[i - 1][k] + S[i - 1][k - 1]

    # Bell number B_n = sum_{k=1..n} S(n, k)
    return sum(S[n][k] for k in range(1, n + 1))


if __name__ == "__main__":
    for i in range(1, 11):
        print(f"holes={i}: partitions={count_partitions(i)} namings={count_partitions(i)*(i+1)}")
# num namings is i + 1 since we can choose either none or one of the partitions to be labels. be careful since num partitions can be zero i guess idk 

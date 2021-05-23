import base64
import random
import math


# RSA public and private keys for signature generation
program_public_key = (107981, 193339)
program_private_key = 134693


# Downloads factorbase from "prime.txt"
def download_factorbase(filename):
    f = open(filename)
    base = f.read().split(" ")
    intbase = []
    for i in base:
        intbase.append(int(i))
    f.close()
    return intbase


# Generates RSA keys using the list of primes
def generate_RSA_keys(primes):
    p_index = random.randint(2, len(primes) - 2)
    q_index = random.randint(2, len(primes) - 2)
    p = primes[p_index]
    q = primes[q_index]
    N = p * q
    phi = (p - 1) * (q - 1)
    e = 0
    while math.gcd(e, phi) != 1:
        e = random.randint(2, phi)
    d = pow(e, -1, phi)
    return e, N, d


# Generates a signature on the RSA key of the program
def sign_RSA(message):
    if message > program_public_key[1]:
        print("Impossible to sign. Message too large.")
        return 0
    signature = (message ** program_private_key) % program_public_key[1]
    return signature


# Verifies a signature
def verif_sign_RSA(m, s):
    m1 = (s ** program_public_key[0]) % program_public_key[1]
    if m1 == m:
        return True
    return False


# Asks for a size of required primes and makes a list of possible primes
def generate_primes_list():
    factorbase = download_factorbase("primes.txt")
    print("Registration mode activated.")
    print("Enter size of p and q in bits: ")
    s_bits = int(input())
    prime_floor = 2 ** (s_bits - 1)
    prime_ceil = 2 ** s_bits - 1
    while prime_ceil > factorbase[len(factorbase) - 1]:
        print("Unfortunately, the size is too large due to limited factorbase...")
        print("Try again:")
        s_bits = int(input())
        prime_floor = 2 ** (s_bits - 1)
        prime_ceil = 2 ** s_bits - 1
    print("size = ", s_bits)
    print("Lowest border of p = ", prime_floor)
    print("Highest border of p = ", prime_ceil)
    suitable_primes = []
    for prime in factorbase:
        if prime < prime_floor:
            continue
        if prime > prime_ceil:
            break
        suitable_primes.append(prime)
    print("List of possible prime numbers is downloaded.")
    return suitable_primes


# Generates Rabin cryptosystem keys to encrypt passwords
def generate_rabin_keys(primes):
    p = primes[random.randint(2, len(primes) - 1)]
    q = primes[random.randint(2, len(primes) - 1)]
    N = p * q
    private_key = (p, q)
    public_key = N
    signature = sign_RSA(public_key)
    print(verif_sign_RSA(public_key, signature))
    pk_file = open("user_public_key.txt", "w")
    pk_file.write('{0}\n'.format(public_key))
    pk_file.write('{0}\n'.format(signature))
    pk_file.close()
    print("Enter password to protect private key:")
    password_sk = int(input())
    sk_file = open("user_private_key.txt", "w")
    sk_file.write('{0}\n'.format(password_sk))
    sk_file.write('{0}\n'.format(private_key[0]))
    sk_file.write('{0}\n'.format(private_key[1]))
    sk_file.close()
    return public_key, private_key


# Retrieves public key from file
def restore_public_key(filename):
    pk_file = open(filename)
    pk = int(pk_file.readline())
    sign = int(pk_file.readline())
    if not verif_sign_RSA(pk, sign):
        print("Incorrect program key. Signature not verified")
        return 0
    return pk


# Retrieves private key from file
def restore_private_key(filename):
    sk_file = open(filename)
    print("Enter password to view private key")
    entered_password = int(input())
    actual_password = int(sk_file.readline())
    if entered_password != actual_password:
        print("Incorrect password")
        return 0
    p = int(sk_file.readline())
    q = int(sk_file.readline())
    return p, q


# Encrypts password using Rabin algorithm
def encrypt_rabin(password, filename):
    N = restore_public_key(filename)
    m = int.from_bytes(password.encode('utf-8'), 'big')
    if m < math.sqrt(N) or m > N:
        print("Incorrect message. Impossible to encrypt.")
        return 0
    c = (m ** 2) % N
    return c


# Decrypts password using Rabin algorithm
def decrypt_rabin(ciphertext, filename):
    p, q = restore_private_key(filename)
    c = int(str(base64.b32decode(ciphertext))[2:-1])
    c_p = c % p
    c_q = c % q
    m_p_1, m_p_2 = solve_congruence_modulo_prime(c_p, p)
    m_q_1, m_q_2 = solve_congruence_modulo_prime(c_q, q)
    m_1 = (m_p_1 * q * pow(q, -1, p) + m_q_1 * p * pow(p, -1, q)) % N
    m_2 = (m_p_2 * q * pow(q, -1, p) + m_q_2 * p * pow(p, -1, q)) % N
    m_3 = (m_p_1 * q * pow(q, -1, p) - m_q_1 * p * pow(p, -1, q)) % N
    m_4 = (m_p_2 * q * pow(q, -1, p) - m_q_2 * p * pow(p, -1, q)) % N
    possible_passwords = []
    possible_passwords.append(m_1)
    possible_passwords.append(m_2)
    possible_passwords.append(m_3)
    possible_passwords.append(m_4)
    print(possible_passwords)
    return possible_passwords


# Solves x^2 = a (mod p)
def solve_congruence_modulo_prime(a, p):
    phi = p - 1
    m = 0
    while phi % 2 == 0:
        phi // 2
        m += 1
    phi = p - 1
    s = phi // (2 ** m)
    b = 0
    for i in range(2, phi):
        if pow(i, phi // 2, p) == -1 % p:
            b = i
    B = pow(b, s, p)
    j = 0
    if m > 1:
        A_i = {}
        B_i = {}
        j_t = {}
        A = pow(a, s, p)
        for i in range(0, m - 1):
            A_i[i] = pow(A, 2 ** i, p)
            B_i[i] = pow(B, 2 ** i, p)
        for t in range(0, m - 1):
            eps_t = A[(m - 2) - t]
            for j in range(0, t):
                eps_t *= pow(B[(m - 2) - (t - 1)], j_t[j])
            j_t[t] = (1 - eps_t) // 2
        j = j_t[0]
        for t in range(m - 1):
            j += (2 ** t) * j[t]
    x1 = (B ** j * a ** ((s + 1) // 2)) % p
    x2 = (- x1) % p
    return x1, x2


while True:
    print("Choose mode...\n\t1: user registration\n\t2: password encryption")
    print("\t3: password decryption\n\t4: programme public key change")
    mode = input()
    while mode != '1' and mode != '2' and mode != '3' and mode != '4':
        print("Incorrect mode. Try again:")
        mode = input()
    if mode == '1':
        print("User registration mode activated.")
        generate_rabin_keys(generate_primes_list())
        print("Keys successfully stored in user_private_key.txt and user_public_key.txt")
    if mode == '2':
        print("Password encryption mode activated.")
        print("Enter filename for user's public key")
        pk_filename = input()
        print("Enter password to encrypt:")
        password = input()
        ciphertext = encrypt_rabin(password, pk_filename)
        print(ciphertext, type(ciphertext))
        if ciphertext != 0:
            ciphertext_encoded = base64.b32encode(str(ciphertext).encode("utf-8")).decode("utf-8")
            print("Ciphertext is", ciphertext_encoded)
            ct_doc = open("ciphertext.txt", "w")
            ct_doc.write('{0}\n'.format(ciphertext_encoded))
            ct_doc.close()
            print("Ciphertext is stored in ciphertext.txt for further reference")
        else:
            print("Error occurred. Impossible to retrieve ciphertext.")
    if mode == '3':
        print("Password decryption mode activated.")
        ct_doc = open("ciphertext.txt", "r")
        ciphertext_encoded = ct_doc.readline()[2:-2]
        ct_doc.close()
        print("Encoded c = ", ciphertext_encoded)
        print("Enter filename for user's public key")
        sk_filename = input()
        passwords = decrypt_rabin(ciphertext_encoded, sk_filename)
        if len(passwords) != 0:
            print("Possible passwords are", passwords)
        else:
            print("Error occurred")
    if mode == '4':
        print("Program keys are being updated")
        e, N, d = generate_RSA_keys(generate_primes_list())
        program_public_key = (e, N)
        program_private_key = d
        print("e, N, d", program_public_key, program_private_key)
    print()
    print("Program finished")
    print("Press Enter to restart")
    input()


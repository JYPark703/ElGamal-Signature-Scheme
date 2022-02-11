/*Final Exam_Question 15
Implement the ElGamal Signature Scheme
Name: Jin Young Park*/

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <ctype.h>
#include <math.h>
#include <time.h>
#include <openssl/sha.h>
#include <openssl/rand.h>
#include <openssl/bn.h>

int e1, e2;
int p, d;
int S1, S2;

unsigned char iv[8];
const unsigned char* A_key = (const unsigned char*)"Password";
int A_key_len = strlen((const char*)A_key);

FILE* out1, * out2;
char* p_path[50], * s1_path[50], * s2_path[50];

int gcd(int a, int b)
{
	int q, r1, r2, r;

	if (a > b) {
		r1 = a;
		r2 = b;
	}
	else {
		r1 = b;
		r2 = a;
	}

	while (r2 > 0) {
		q = r1 / r2;
		r = r1 - q * r2;
		r1 = r2;
		r2 = r;
	}

	return r1;
}

int FastExponention(int bit, int n, int* y, int* a)
{
	if (bit == 1)
		*y = (*y * (*a)) % n;

	*a = (*a) * (*a) % n;
	return 0;
}

int FindT(int a, int m, int n)
{
	int r;
	int y = 1;

	while (m > 0)
	{
		r = m % 2;
		FastExponention(r, n, &y, &a);
		m = m / 2;
	}

	return y;
}

int PrimarityTest(int a, int i)
{
	int n = i - 1;
	int k = 0;
	int m, T;

	while (n % 2 == 0) {
		k++;
		n = n / 2;
	}

	m = n;
	T = FindT(a, m, i);
	if (T == 1 || T == i - 1)
		return 1;

	for (int j = 0; j < k; j++) {
		T = FindT(T, 2, i);
		if (T == 1)
			return 0;
		if (T == i - 1)
			return 1;
	}

	return 0;
}

int PrimitiveRoot(int p)
{
	int flag;
	for (int a = 2; a < p; a++)
	{
		flag = 1;
		for (int i = 1; i < p; i++) {
			if (FindT(a, i, p) == 1 && i < p - 1) {
				flag = 0;
			}
			else if (flag && FindT(a, i, p) == 1 && i == p - 1) {
				return a;
			}
		}
	}
}

int Extended_Euclid(int r1, int r2)
{
	int r, q, s, s1 = 1, s2 = 0, t, t1 = 0, t2 = 1, tmp = r1;

	while (r2)
	{
		q = r1 / r2;
		r = r1 % r2;
		s = s1 - q * s2;
		t = t1 - q * t2;


		r1 = r2;
		r2 = r;
		s1 = s2;
		s2 = s;
		t1 = t2;
		t2 = t;
	}

	if (s1 < 0) {
		s1 = r2 + s1;
	}

	return s1;
}


/*Functions that execute HMAC using SHA256 (hash function)*/
void hmac_sha256(unsigned char* message, int messagelength, unsigned char* iv, unsigned char* tag)    /* caller digest to be filled in */
{

	unsigned char k_ipad[65];
	unsigned char k_opad[65];
	unsigned char tk[SHA256_DIGEST_LENGTH];
	unsigned char tk2[SHA256_DIGEST_LENGTH];
	unsigned char tk3[SHA256_DIGEST_LENGTH];
	unsigned char messagebuffer[1024];
	unsigned char bufferIn[1024];
	unsigned char bufferOut[1024];
	unsigned char length[1];
	length[0] = (unsigned char)messagelength;
	int i;

	/* if key is longer than 64 bytes reset it to key=sha256(key) */
	if (A_key_len > 64) {
		SHA256(A_key, A_key_len, tk);
		A_key = tk;
		A_key_len = SHA256_DIGEST_LENGTH;
	}


	/* start out by storing key in pads */
	memset(k_ipad, 0, sizeof k_ipad);
	memset(k_opad, 0, sizeof k_opad);
	memcpy(k_ipad, A_key, A_key_len);
	memcpy(k_opad, A_key, A_key_len);

	/* XOR key with ipad and opad values */
	for (i = 0; i < 64; i++) {
		k_ipad[i] ^= 0x36;
		k_opad[i] ^= 0x5c;
	}


	/*
	 * perform inner SHA256
	 */
	memset(bufferIn, 0x00, 1024);
	memcpy(bufferIn, k_ipad, 64);
	memcpy(bufferIn + 64, iv, 8);

	SHA256(bufferIn, 64 + 8, tk2);


	if (messagelength < 1024 - SHA256_DIGEST_LENGTH) {
		memset(bufferIn, 0x00, 1024);
		memcpy(bufferIn, tk2, SHA256_DIGEST_LENGTH);
		memcpy(bufferIn + SHA256_DIGEST_LENGTH, message, messagelength);

		SHA256(bufferIn, 1024, tk2);
	}
	else {
		for (i = 0; i < messagelength - (1024 - SHA256_DIGEST_LENGTH); i += (1024 - SHA256_DIGEST_LENGTH)) {
			memset(bufferIn, 0x00, 1024);
			memcpy(bufferIn, tk2, SHA256_DIGEST_LENGTH);
			memcpy(bufferIn + SHA256_DIGEST_LENGTH, message + i, 1024 - SHA256_DIGEST_LENGTH);
			SHA256(bufferIn, 1024, tk2);
		}
		memset(bufferIn, 0x00, 1024);
		memcpy(bufferIn, tk2, SHA256_DIGEST_LENGTH);
		memcpy(bufferIn + SHA256_DIGEST_LENGTH, message + i, messagelength - i);

		SHA256(bufferIn, 1024, tk2);
	}

	memset(bufferIn, 0x00, 1024);
	memcpy(bufferIn, tk2, SHA256_DIGEST_LENGTH);
	memcpy(bufferIn + SHA256_DIGEST_LENGTH, length, 1);
	SHA256(bufferIn, SHA256_DIGEST_LENGTH + 1, tk2);

	/*
	 * perform outer SHA256
	 */

	memset(bufferOut, 0x00, 1024);
	memcpy(bufferOut, k_opad, 64);
	memcpy(bufferIn + 64, iv, 8);
	SHA256(bufferIn, 64 + 8, tk3);


	memset(bufferIn, 0x00, 1024);
	memcpy(bufferIn, tk2, SHA256_DIGEST_LENGTH);
	memcpy(bufferOut + SHA256_DIGEST_LENGTH, tk3, SHA256_DIGEST_LENGTH);
	SHA256(bufferOut, SHA256_DIGEST_LENGTH + SHA256_DIGEST_LENGTH, tag);
}

/*Generate key (d, p, e1, e2)*/
int KeyGeneration()
{
	/*Generate prime number p*/
	do {
		do {
			BIGNUM* bn = BN_new();
			BN_generate_prime_ex(bn, 31, 1, NULL, NULL, NULL);
			char* ch = BN_bn2dec(bn);
			p = atoi(ch)%1024;
		} while (p % 2 == 0);

	} while (!PrimarityTest(2, p));
	
	/*Set e1*/
	e1 = 2;

	/*Randomly choose the privete key d, 1 <= d <= p-2*/
	do {
		BIGNUM* bn = BN_new();
		BN_rand(bn, 31, 0, 1);
		char* ch = BN_bn2dec(bn);
		d = atoi(ch) % (p - 2) + 1; // 1 <= d <= p-2
	} while (gcd(d, p) != 1);

	/*Calculate e2*/
	e2 = FindT(e1, d, p); //e2=(e1^d)mod p
	return 0;
}

/*Sign the hashed plaintext*/
int Sign(int h_Plaintext)
{
	out1 = fopen((const char*)s1_path, "a+"); //C:\\Result\\sign1.txt
	out2 = fopen((const char*)s2_path, "a+"); //C:\\Result\\sign2.txt

	/*generate random number r*/
	int r;
	do {
		r = rand() % (p - 2) + 1; // 1 < r < p-1
	} while (gcd(r, p - 1) != 1);


	S1 = FindT(e1, r, p); //s1=(e1^r)mod p
	S2 = ((h_Plaintext - d * S1) * Extended_Euclid(r, p - 1)) % (p - 1); //S2=((m-d*s1)*(r^-1))mod (p-1)
	if (S2 < 0) {  //If S2 is negative number, then change to positive number.
		S2 = p - 1 + S2;
	}

	fprintf(out1, "%d ", S1); //Write S1 to the file which store the first signature
	fprintf(out2, "%d ", S2); //Write S2 to the file which store the second signature

	fclose(out1);
	fclose(out2);
	return 0;
}

/*Verify the hashed plaintext*/
int Verify(int S1, int S2, int h_Plaintext)
{

	int V1, V2;
	V1 = FindT(e1, h_Plaintext, p); //V1=(e1^m)mod p
	V2 = (FindT(e2, S1, p) * FindT(S1, S2, p)) % p; //V2=((e2^S1)*(S1*S2))mod p
	
	if (V1 == V2) { //If V1 and V2 is same, then return 1
		return 1;
	}
	else { //If V1 and V2 is different, then return 0
		return 0;
	}

}

int main()
{
	FILE* out, * inp;

	/*Enter the path of the file to be encrypted, the path to store ciphertext, and the path to store the decrypted message.*/
	printf("Enter the path of the file to be plaintext: ");
	scanf("%s", p_path);
	printf("Enter the path to store the first signature(S1): ");
	scanf("%s", s1_path);
	printf("Enter the path to store the second signature(S2): ");
	scanf("%s", s2_path);

	/*Set file path*/
	out = fopen((const char*)s1_path, "w+");
	fclose(out);
	out = fopen((const char*)s2_path, "w+");
	fclose(out);
	inp = fopen((const char*)p_path, "r+"); 
	if (inp == NULL) {
		printf("Error opening Source File.\n");
		exit(1);
	}

	/*Read file data*/
	unsigned char* sign_message;
	unsigned char sign_hash[SHA256_DIGEST_LENGTH];
	
	int size1;
	int count1;

	fseek(inp, 0, SEEK_END);
	size1 = ftell(inp);

	sign_message = (unsigned char*)malloc(size1 + 1);
	memset(sign_message, 0, size1 + 1);

	fseek(inp, 0, SEEK_SET);
	count1 = fread(sign_message, size1, 1, inp);


	/*Generate key d, p, e1, e2*/
	clock_t start_k = clock();//Store Key generation start time
	KeyGeneration();
	clock_t end_k = clock();//Store Key generation end time

	/*Generate random iv*/
	RAND_status();
	RAND_bytes(iv, 8);

	/*Execute the hash function with the plaintext*/
	clock_t start_s = clock();//Store Sign start time
	hmac_sha256((unsigned char*)sign_message, size1, (unsigned char*)iv, (unsigned char*)sign_hash);

	/*Sign with the hashed plaintext and private key e1, d, p*/
	for (int i = 0; i < SHA256_DIGEST_LENGTH; i++)
	{
		Sign(sign_hash[i]);
	}
	clock_t end_s = clock();//Store Sign end time
	fclose(inp);


	/*Set file path*/
	FILE* inp1, * inp2;
	inp1 = fopen((const char*)s1_path, "r"); 
	inp2 = fopen((const char*)s2_path, "r"); 
	inp = fopen((const char*)p_path, "r+"); 
	if (inp == NULL) {
		printf("Error opening Source File.\n");
		exit(1);
	}

	/*Read file data*/
	unsigned char* vrfy_message;
	unsigned char vrfy_hash[SHA256_DIGEST_LENGTH];
	int size2;
	int count2;

	fseek(inp, 0, SEEK_END);
	size2 = ftell(inp);

	vrfy_message = (unsigned char*)malloc(size2 + 1);
	memset(vrfy_message, 0, size2 + 1);

	fseek(inp, 0, SEEK_SET);
	count2 = fread(vrfy_message, size2, 1, inp);

	/*Execute the hash function with the plaintext*/
	clock_t start_v = clock();//Store Verify start time
	hmac_sha256((unsigned char*)vrfy_message, size2, (unsigned char*)iv, (unsigned char*)vrfy_hash);

	/*Verify with the hashed plaintext and private key e1,e2, p*/
	int S1, S2;
	for (int i = 0; i < SHA256_DIGEST_LENGTH; i++)
	{
		int ret = fscanf(inp1, "%d", &S1);
		fscanf(inp2, "%d", &S2);
		if (ret == -1)
			break;
		/*If the hashed plaintext and the recieved message are different, print "error" and exit the program*/
		if (!Verify(S1, S2, vrfy_hash[i])) {
			printf("error");
			fclose(inp1);
			fclose(inp2);

			return 0;

		}
	}
	clock_t end_v = clock();//Store Verify end time

	/*If the hashed plaintext and the recieved message are same, print "Verifyint is Success"*/
	printf("Verifing is Success!!\n");
	/*Output encryption and decryption running time*/
	printf("Key generation time: %lf, Sign time: %lf, Verify time: %lf\n", (double)(end_k - start_k) / CLOCKS_PER_SEC, (double)(end_s - start_s) / CLOCKS_PER_SEC, (double)(end_v - start_v) / CLOCKS_PER_SEC);

	fclose(inp1);
	fclose(inp2);

	return 0;
}
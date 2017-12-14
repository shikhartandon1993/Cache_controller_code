/////CACHE PROJECT EE6313
///SHIKHAR TANDON
///ABHISHEKH ANAND
#include<math.h>
#include<conio.h>
#include<stdio.h>
#include<stdint.h>
#define NRANSI
#include "nrutil.h"

#pragma align(32)
//#include "nr.h"
#define ROTATE(a,i,j,k,l) g=a[i][j];h=a[k][l];a[i][j]=g-s*(h+g*tau);\
	a[k][l]=h+s*(g-h*tau);



#define MAX_LINES 16384
#define MAX_WAYS 16
#define MAX_BL 8



int isDirty(uint32_t, int);
void clearDirty(uint32_t, int);
void invalidate(uint32_t, int);
void readMemory(void*, int);
void readBlock(void*, uint32_t, int);
void validate(uint32_t, int);
void writeMemory(void*, int);
void writeLine(void*);

int lru[MAX_LINES][MAX_WAYS];
int dirty[MAX_LINES][MAX_WAYS];
int valid[MAX_LINES][MAX_WAYS];
uint32_t tag1[MAX_LINES][MAX_WAYS];

//counters
int read_mem_count;
int read_line_count;
int read_miss_count;
int read_dirty_replace_count;
int read_cache_count;

int write_mem_count;
int write_line_count;
int write_line_miss;
int write_dirty_replace_count;
int write_cache_count;
int write_thru_mem_count;
int write_block_time;
int check_count;
int hit_count;
int flush_count;


uint64_t hit_time;
uint64_t read_block_time;
uint64_t total_access_time;



int w = 32;//4 bytes
int BL;
int N;
int B;
uint32_t L;
int strat;

uint32_t row;
int col;

void init()
{

	//counters
	read_mem_count = 0;
	read_line_count = 0;
	read_miss_count = 0;
	read_dirty_replace_count = 0;
	read_cache_count = 0;

	write_mem_count = 0;
	write_line_count = 0;
	write_line_miss = 0;
	write_dirty_replace_count = 0;
	write_cache_count = 0;
	write_thru_mem_count = 0;
	write_block_time = 0;
	check_count = 0;
	hit_count = 0;
	flush_count = 0;

	hit_time = 0;
	read_block_time = 0;
	total_access_time = 0;

	for (row = 0; row < MAX_LINES; row++)
	{
		for (col = 0; col < MAX_WAYS; col++)
		{
			lru[row][col] = col;
			dirty[row][col] = 0;
			valid[row][col] = 0;
			tag1[row][col] = -1;
		}
	}
}



void jacobi(double **a, int n, double d[], double **v, int *nrot)
{
	int j, iq, ip, i;
	double tresh, theta, tau, t, sm, s, h, g, c, *b, *z;

	readMemory(&n, sizeof(n));
	writeMemory(&b, sizeof(b));
	b = vector(1, n);
	readMemory(&n, sizeof(n));
	writeMemory(&z, sizeof(z));
	z = vector(1, n);

	writeMemory(&ip, sizeof(ip));
	readMemory(&ip, sizeof(ip));
	readMemory(&n, sizeof(n));
	for (ip = 1; ip <= n; ip++)
	{ //Initialize to the identity matrix.

		writeMemory(&iq, sizeof(iq));
		readMemory(&iq, sizeof(iq));
		readMemory(&n, sizeof(n));
		for (iq = 1; iq <= n; iq++)
		{
			readMemory(&ip, sizeof(ip));
			readMemory(&iq, sizeof(iq));
			writeMemory(&v[ip][iq], sizeof(v[ip][iq]));

			v[ip][iq] = 0.0;

			//iq++
			readMemory(&iq, sizeof(iq));
			writeMemory(&iq, sizeof(iq));//iq<-iq+1
			readMemory(&iq, sizeof(iq));//compare iq with n
			readMemory(&n, sizeof(n));//compare with n

		}

		readMemory(&ip, sizeof(ip));
		writeMemory(&v[ip][ip], sizeof(v[ip][ip]));
		v[ip][ip] = 1.0;

		//ip++
		readMemory(&ip, sizeof(ip));
		writeMemory(&ip, sizeof(ip));//ip <- ip+1
		readMemory(&ip, sizeof(ip));//compare with n
		readMemory(&n, sizeof(n));


	}

	writeMemory(&ip, sizeof(ip));
	readMemory(&ip, sizeof(ip));
	readMemory(&n, sizeof(n));
	for (ip = 1; ip <= n; ip++)
	{

		readMemory(&ip, sizeof(ip));
		readMemory(&a[ip][ip], sizeof(a[ip][ip]));
		writeMemory(&d[ip], sizeof(d[ip]));
		readMemory(&d[ip], sizeof(d[ip]));
		writeMemory(&b[ip], sizeof(b[ip]));


		b[ip] = d[ip] = a[ip][ip]; 

		readMemory(&ip, sizeof(ip));
		writeMemory(&z[ip], sizeof(z[ip]));
		z[ip] = 0.0; 

		//ip++
		readMemory(&ip, sizeof(ip));
		writeMemory(&ip, sizeof(ip));
		readMemory(&ip, sizeof(ip));
		readMemory(&n, sizeof(n));

	}

	readMemory(&nrot, sizeof(nrot));
	writeMemory(nrot, sizeof(*nrot));
	*nrot = 0;

	writeMemory(&i, sizeof(i));
	readMemory(&i, sizeof(i));
	for (i = 1; i <= 50; i++)
	{
		writeMemory(&sm, sizeof(sm));
		sm = 0.0;

		writeMemory(&ip, sizeof(ip));
		readMemory(&ip, sizeof(ip));
		readMemory(&n, sizeof(n));
		for (ip = 1; ip <= n - 1; ip++)
		{
			//Sum off-diagonal elements.
			readMemory(&ip, sizeof(ip));
			writeMemory(&iq, sizeof(iq));
			readMemory(&iq, sizeof(iq));
			readMemory(&n, sizeof(n));
			for (iq = ip + 1; iq <= n; iq++)
			{
				readMemory(&sm, sizeof(sm));
				readMemory(&ip, sizeof(ip));
				readMemory(&iq, sizeof(iq));
				readMemory(&a[ip][iq], sizeof(a[ip][iq]));
				writeMemory(&sm, sizeof(sm));
				sm += fabs(a[ip][iq]);

				//iq++
				readMemory(&iq, sizeof(iq));
				writeMemory(&iq, sizeof(iq));//iq <- iq+1
				readMemory(&iq, sizeof(iq));	//compare with n		
				readMemory(&n, sizeof(n));
			}

			//ip++
			readMemory(&ip, sizeof(ip));
			writeMemory(&ip, sizeof(ip));//ip <- ip+1
			readMemory(&ip, sizeof(ip));//compare with n
			readMemory(&n, sizeof(n));
		}

		readMemory(&sm, sizeof(sm));
		if (sm == 0.0)
		{ //The normal return, which relies on quadratic convergence to machine underflow.
			readMemory(&z, sizeof(z));
			readMemory(&n, sizeof(n));
			free_vector(z, 1, n);

			readMemory(&b, sizeof(b));
			readMemory(&n, sizeof(n));
			free_vector(b, 1, n);
			return;
		}

		//if condition
		readMemory(&i, sizeof(i));
		if (i < 4)
		{
			readMemory(&sm, sizeof(sm));
			readMemory(&n, sizeof(n));
			writeMemory(&tresh, sizeof(tresh));
			tresh = 0.2*sm / (n*n); //...on the first three sweeps.
		}
		else
		{
			writeMemory(&tresh, sizeof(tresh));
			tresh = 0.0; //...thereafter.
		}

		writeMemory(&ip, sizeof(ip));
		readMemory(&ip, sizeof(ip));
		readMemory(&n, sizeof(n));
		for (ip = 1; ip <= n - 1; ip++)
		{
			readMemory(&ip, sizeof(ip));
			writeMemory(&iq, sizeof(iq));
			readMemory(&iq, sizeof(iq));
			readMemory(&n, sizeof(n));
			for (iq = ip + 1; iq <= n; iq++)
			{
				readMemory(&ip, sizeof(ip));
				readMemory(&iq, sizeof(iq));
				readMemory(&a[ip][iq], sizeof(a[ip][iq]));
				writeMemory(&g, sizeof(g));
				g = 100.0*fabs(a[ip][iq]);
				// After four sweeps, skip the rotation if the off-diagonal element is small.

				//for if condition
				readMemory(&i, sizeof(i));//i>4
				readMemory(&ip, sizeof(ip));
				readMemory(&d[ip], sizeof(d[ip]));//d[ip]
				readMemory(&g, sizeof(g));//g
				readMemory(&iq, sizeof(iq));//iq
				readMemory(&d[iq], sizeof(d[iq]));//d[iq]

				//for else if condition
				readMemory(&ip, sizeof(ip));
				readMemory(&iq, sizeof(iq));
				readMemory(&tresh, sizeof(tresh));

				if (i > 4 && (double)(fabs(d[ip]) + g) == (double)fabs(d[ip]) && (double)(fabs(d[iq]) + g) == (double)fabs(d[iq]))
				{
					readMemory(&ip, sizeof(ip));
					readMemory(&iq, sizeof(iq));
					writeMemory(&a[ip][iq], sizeof(a[ip][iq]));
					a[ip][iq] = 0.0;
				}
				else if (fabs(a[ip][iq]) > tresh)
				{
					readMemory(&iq, sizeof(iq));
					readMemory(&d[iq], sizeof(d[iq]));
					readMemory(&ip, sizeof(ip));
					readMemory(&d[ip], sizeof(d[ip]));
					writeMemory(&h, sizeof(h));
					h = d[iq] - d[ip];

					//if condition
					readMemory(&h, sizeof(h));
					readMemory(&g, sizeof(g));


					if ((double)(fabs(h) + g) == (double)fabs(h))
					{
						readMemory(&ip, sizeof(ip));
						readMemory(&iq, sizeof(iq));
						readMemory(&a[ip][iq], sizeof(a[ip][iq]));
						readMemory(&h, sizeof(h));
						writeMemory(&t, sizeof(t));

						t = (a[ip][iq]) / h;
					}
					else
					{
						readMemory(&h, sizeof(h));
						readMemory(&ip, sizeof(ip));
						readMemory(&iq, sizeof(iq));
						readMemory(&a[ip][iq], sizeof(a[ip][iq]));
						writeMemory(&theta, sizeof(theta));

						theta = 0.5*h / (a[ip][iq]);

						readMemory(&theta, sizeof(theta));
						writeMemory(&t, sizeof(t));

						t = 1.0 / (fabs(theta) + sqrt(1.0 + theta*theta));

						readMemory(&theta, sizeof(theta));
						if (theta < 0.0)
						{
							readMemory(&t, sizeof(t));
							writeMemory(&t, sizeof(t));

							t = -t;
						}
					}

					readMemory(&t, sizeof(t));
					writeMemory(&c, sizeof(c));

					c = 1.0 / sqrt(1 + t*t);

					readMemory(&c, sizeof(c));
					readMemory(&t, sizeof(t));
					writeMemory(&s, sizeof(s));

					s = t*c;

					readMemory(&s, sizeof(s));
					readMemory(&c, sizeof(c));
					writeMemory(&tau, sizeof(tau));

					tau = s / (1.0 + c);

					readMemory(&ip, sizeof(ip));
					readMemory(&iq, sizeof(iq));
					readMemory(&a[ip][iq], sizeof(a[ip][iq]));
					readMemory(&t, sizeof(t));
					writeMemory(&h, sizeof(h));

					h = t*a[ip][iq];

					readMemory(&ip, sizeof(ip));
					readMemory(&z[ip], sizeof(z[ip]));
					readMemory(&h, sizeof(h));
					writeMemory(&z[ip], sizeof(z[ip]));

					z[ip] -= h;

					readMemory(&iq, sizeof(iq));
					readMemory(&z[iq], sizeof(z[iq]));
					readMemory(&h, sizeof(h));
					writeMemory(&z[iq], sizeof(z[iq]));

					z[iq] += h;

					readMemory(&ip, sizeof(ip));
					readMemory(&d[ip], sizeof(d[ip]));
					readMemory(&h, sizeof(h));
					writeMemory(&d[ip], sizeof(d[ip]));

					d[ip] -= h;

					readMemory(&iq, sizeof(iq));
					readMemory(&d[iq], sizeof(d[iq]));
					readMemory(&h, sizeof(h));
					writeMemory(&d[iq], sizeof(d[iq]));

					d[iq] += h;

					readMemory(&ip, sizeof(ip));
					readMemory(&iq, sizeof(iq));
					writeMemory(&a[ip][iq], sizeof(a[ip][iq]));

					a[ip][iq] = 0.0;

					writeMemory(&j, sizeof(j));
					readMemory(&j, sizeof(j));
					readMemory(&ip, sizeof(ip));
					for (j = 1; j <= ip - 1; j++)
					{ //Case of rotations 1 <= j<p.
						readMemory(&a, sizeof(a));
						readMemory(&j, sizeof(j));
						readMemory(&ip, sizeof(ip));
						readMemory(&iq, sizeof(iq));
						ROTATE(a, j, ip, j, iq)

							//j++
							readMemory(&j, sizeof(j));
						writeMemory(&j, sizeof(j));//j <- j+1
						readMemory(&j, sizeof(j));//compare with ip
						readMemory(&ip, sizeof(ip));
					}

					readMemory(&ip, sizeof(ip));
					writeMemory(&j, sizeof(j));
					readMemory(&j, sizeof(j));
					readMemory(&iq, sizeof(iq));
					for (j = ip + 1; j <= iq - 1; j++)
					{ //Case of rotations p<j<q.
						readMemory(&a, sizeof(a));
						readMemory(&ip, sizeof(ip));
						readMemory(&j, sizeof(j));
						readMemory(&iq, sizeof(iq));
						ROTATE(a, ip, j, j, iq)

							//j++
							readMemory(&j, sizeof(j));
						writeMemory(&j, sizeof(j));//j <- j+1
						readMemory(&j, sizeof(j));//compare with ip
						readMemory(&iq, sizeof(iq));
					}

					readMemory(&iq, sizeof(iq));
					writeMemory(&j, sizeof(j));
					readMemory(&j, sizeof(j));
					readMemory(&n, sizeof(n));
					for (j = iq + 1; j <= n; j++)
					{ //Case of rotations q<j <= n.
						readMemory(&a, sizeof(a));
						readMemory(&ip, sizeof(ip));
						readMemory(&j, sizeof(j));
						readMemory(&iq, sizeof(iq));
						ROTATE(a, ip, j, iq, j)

							//j++
							readMemory(&j, sizeof(j));
						writeMemory(&j, sizeof(j));//j <- j+1
						readMemory(&j, sizeof(j));//compare with ip
						readMemory(&n, sizeof(n));

					}


					writeMemory(&j, sizeof(j));
					readMemory(&j, sizeof(j));
					readMemory(&n, sizeof(n));
					for (j = 1; j <= n; j++)
					{
						readMemory(&v, sizeof(v));
						readMemory(&j, sizeof(j));
						readMemory(&ip, sizeof(ip));
						readMemory(&iq, sizeof(iq));
						ROTATE(v, j, ip, j, iq)

							//j++
							readMemory(&j, sizeof(j));
						writeMemory(&j, sizeof(j));//j <- j+1
						readMemory(&j, sizeof(j));//compare with ip
						readMemory(&n, sizeof(n));
					}

					writeMemory(nrot, sizeof(*nrot));
					readMemory(nrot, sizeof(*nrot));
					++(*nrot);
				}

				//iq++
				readMemory(&iq, sizeof(iq));
				writeMemory(&iq, sizeof(iq));//iq <- iq+1
				readMemory(&iq, sizeof(iq));	//compare with n		
				readMemory(&n, sizeof(n));
			}

			//ip++
			readMemory(&ip, sizeof(ip));
			writeMemory(&ip, sizeof(ip));//ip <- ip+1
			readMemory(&ip, sizeof(ip));//compare with n
			readMemory(&n, sizeof(n));
		}

		writeMemory(&ip, sizeof(ip));
		readMemory(&ip, sizeof(ip));
		readMemory(&n, sizeof(n));
		for (ip = 1; ip <= n; ip++)
		{
			readMemory(&ip, sizeof(ip));
			readMemory(&b[ip], sizeof(b[ip]));
			readMemory(&z[ip], sizeof(z[ip]));
			writeMemory(&b[ip], sizeof(b[ip]));
			b[ip] += z[ip];

			readMemory(&ip, sizeof(ip));
			readMemory(&b[ip], sizeof(b[ip]));
			writeMemory(&d[ip], sizeof(d[ip]));
			d[ip] = b[ip]; //Update d with the sum of tapq,

			readMemory(&ip, sizeof(ip));
			writeMemory(&z[ip], sizeof(z[ip]));
			z[ip] = 0.0; //and reinitialize z.
			
						 // ip++
			readMemory(&ip, sizeof(ip));
			writeMemory(&ip, sizeof(ip));//ip <- ip+1
			readMemory(&ip, sizeof(ip));//compare with n
			readMemory(&n, sizeof(n));
		}

		readMemory(&i, sizeof(i));
		writeMemory(&i, sizeof(i));
		readMemory(&i, sizeof(i));
	}
	nrerror("Too many iterations in routine jacobi");
}








int logt(int x)
{
	int i = 2, count = 0;
	if (x == 1)
		return 0;
	else
	{
		while (i <= x)
		{
			i *= 2;
			count++;
		}
	}
	return count;
}

uint32_t getLine(uint32_t addr)
{

	uint32_t num, line;
	int t = w - logt(L) - logt(B);
	line = (addr << t) >> (t + logt(B));
	return line;
}

uint32_t getTag(uint32_t addr)
{
	uint32_t num, tag;
	//num = *((uint32_t*)(&addr));
	tag = addr >> (logt(B) + logt(L));
	return tag;
}

int getWay(uint32_t loc1)
{
	int flag = 0, i;
	uint32_t line1;
	line1 = getLine(loc1);
	for (i = 0; i < N; i++)
	{
		if (tag1[line1][i] == getTag(loc1))
		{
			
			flag = 1;
			return i;
		}

	}

	if (flag == 0)//tag not found in cache
	{
		
		return -1;
	}

}

void empty_cac()
{
	uint64_t i;
	int j;
	for (i = 0; i < MAX_LINES; i++)
	{
		for (j = 0; j < MAX_WAYS; j++)
		{
			if (dirty[i][j] == 1)
			{
				dirty[i][j] = 0;
				flush_count++;
			}
		}
	}

}

int isMiss(void *add_miss)
{

	int wayz;
	uint32_t addres, line, ad;
	ad = (uint32_t)add_miss;
	line = getLine(ad);
	wayz = getWay(ad);
	if (wayz != -1)
	{

		if (getTag(ad) == tag1[line][wayz])
		{
			hit_count++;
			return 0;
		}
		else
		{
			return 1;
		}

	}


	return 1;
}

int getLRUway(uint32_t line)
{
	int i, j, max = -1;
	if (N == 1)
	{
		return 0;
	}
	else
	{
		for (i = 0; i < N; i++)
		{

			if (lru[line][i] > max)
			{
				max = lru[line][i];
				j = i;

			}


		}
		return j;
	}

}

void updateLru(void *add, int flag)
{
	int i, oldest_way, wayz;
	uint32_t line, ad;
	ad = (uint32_t)add;
	line = getLine(ad);

	if (flag == 1)//if its a miss
	{
		oldest_way = getLRUway(line);
		for (i = 0; i<N; i++)
		{
			lru[line][i] += 1;
		}
		lru[line][oldest_way] = 0;
	}
	else//if its a hit
	{
		wayz = getWay(ad);//in which way is the address present
		for (i = 0; i<N; i++)
		{
			lru[line][i] += 1;
		}
		lru[line][wayz] = 0;
	}
}

void readLine(void *addr)
{
	int oldest_way, flag = 0;
	uint32_t line, ad;
	//printf("in read line\n");
	ad = (uint32_t)addr;
	if (isMiss(addr))
	{
		read_miss_count++;
		line = getLine(ad);
		oldest_way = getLRUway(line);//to be done
									 //printf("dirty\n");
		if (isDirty(line, oldest_way))//to be done
		{

			//writeBack(line,oldest_way);//update its counter
			//writeBack_count++;
			clearDirty(line, oldest_way);//decrement dirty count
			read_dirty_replace_count++;
		}
		invalidate(line, oldest_way);
		//read_block_count++;//--->counter increment
		readBlock(addr, line, oldest_way);//read from memory into cache,UPDATE TAG OF CACHE(now we can read from cache)
		validate(line, oldest_way);
		flag = 1;//if miss flag = 1 
	}
	updateLru(addr, flag);
	read_cache_count++;//update read cache counter

}

void readMemory(void *addr, int size)
{

	int i;
	int old_line = -1;
	uint32_t x, line, ad;
	read_mem_count++;
	for (i = 0; i < size; i++)
	{
		ad = (uint32_t)addr + i;
		line = getLine(ad);
		
		if (line != old_line)
		{
			read_line_count++;
			readLine(ad);//read the line to see if its a miss or hit
			old_line = line;
		}

	}
}

void readBlock(void *addr, uint32_t line, int oldest_way)//update the tag in cache if its a read miss
{
	uint32_t ad;
	ad = (uint32_t)addr;
	tag1[line][oldest_way] = getTag(ad);//update the tag in cache if its a read miss	
	read_block_time++;
}

void writeBlock(void *addr, uint32_t line, int oldest_way)//update the tag in cache if its a write miss
{
	uint32_t ad;
	ad = (uint32_t)addr;
	tag1[line][oldest_way] = getTag(ad);//update the tag in cache if its a read miss	
	write_block_time++;
}

int isDirty(uint32_t line, int old_way)
{
	if (dirty[line][old_way] == 1)//if not updated to memory
		return 1;

	else
		return 0;
}

void clearDirty(uint32_t line, int oldest_way)
{
	dirty[line][oldest_way] = 0;
}

void invalidate(uint32_t line_inv, int old_way)
{
	valid[line_inv][old_way] = 0;
}

void validate(uint32_t line_inv, int old_way)
{
	valid[line_inv][old_way] = 1;
}



void writeMemory(void *addr, int size)
{
	int i;
	int old_line = -1;
	uint32_t x, line;
	write_mem_count++;
	if (strat == 2 || strat == 3)
	{
		write_thru_mem_count += (size / 4);//incrementing write through memory count
	}
	for (i = 0; i < size; i++)
	{
		x = (uint32_t)addr + i;

		line = getLine(x);
		if (line != old_line)
		{
			write_line_count++;
			writeLine(x);//write to the line to see if its a miss or hit
			old_line = line;
		}

	}
}


void writeLine(void *addr)
{
	int oldest_way, flag = 0, wayz;
	uint32_t line, ad;
	ad = (uint32_t)addr;

	if (isMiss(addr) && (strat == 1 || strat == 3))//wb or wta miss
	{
		write_line_miss++;
		line = getLine(ad);
		oldest_way = getLRUway(line);//to be done
		if (isDirty(line, oldest_way))//to be done
		{
			//writeBack(line,oldest_way);//update its counter
			//writeBack_count++;
			clearDirty(line, oldest_way);//decrement dirty count
			write_dirty_replace_count++;//dump to memory
		}
		invalidate(line, oldest_way);
		//read_block_count++;//--->counter increment
		writeBlock(addr, line, oldest_way);//read from memory into cache
		validate(line, oldest_way);
		updateLru(addr, 1);//if miss

		write_cache_count++;//update write cache counter
		if (strat == 1)
			dirty[line][oldest_way] = 1;
		//write through count incremented in writeMemory function
	}


	else if (!isMiss(addr) && (strat == 1 || strat == 3)) //wb or wta hit
	{
		write_cache_count++;//update write cache counter

		if (strat == 1)
		{
			line = getLine(ad);
			wayz = getWay(ad);//to be done
			dirty[line][wayz] = 1;//because it writes only to cache
		}

		updateLru(addr, 0);//if hit
	}

	else if (isMiss(addr) && strat == 2)//WTNA miss
	{
		write_line_miss++;		//write through count incremented in writeMemory function.nothing else will happen in WTNA. cache is ignored
	}

	else if (!isMiss(addr) && strat == 2)//WTNA hit
	{

		

		write_cache_count++;
		updateLru(addr, 0);//flag = 0 -- is a hit
		//write through count incremented in writeMemory function

	}


}

void file_init() {// reference from -->https://www.tutorialspoint.com/c_standard_library/c_function_fopen.htm
	FILE *file1;
	file1 = fopen("data_report.xls", "w");
	if (file1 == NULL)
	{
		fprintf(stderr, "file not opened\n");
		exit(1);
	}
	
	fprintf(file1, "strat\tN\tBL\tread_mem_count\tread_line_count\tread_miss_count\tread_dirty_replace_count\tread_cache_count\twrite_mem_count\twrite_line_count\twrite_line_miss\twrite_dirty_replace_count\twrite_cache_count\twrite_thru_mem_count\ttotal_access_time(ns)\n");
	fclose(file1);
}

void file_display() {
	FILE *file1;
	file1 = fopen("data_report.xls", "a");// reference from -->https://www.tutorialspoint.com/c_standard_library/c_function_fopen.htm
	if (file1 == NULL)
	{
		fprintf(stderr, "file not opened\n");
		exit(1);
	}

	fprintf(file1,"%d\t",strat);
	fprintf(file1, "%d\t", N);
	fprintf(file1, "%d\t",BL);
	fprintf(file1, "%d\t", read_mem_count);
	fprintf(file1, "%d\t", read_line_count);
	fprintf(file1, "%d\t", read_miss_count);
	fprintf(file1, "%d\t", read_dirty_replace_count);
	fprintf(file1, "%d\t", read_cache_count);
	fprintf(file1, "%d\t", write_mem_count);
	fprintf(file1, "%d\t", write_line_count);
	fprintf(file1, "%d\t", write_line_miss);
	fprintf(file1, "%d\t", write_dirty_replace_count);//because write through memory has 4 byte writes only
	fprintf(file1, "%d\t", write_cache_count);
	fprintf(file1, "%d\t", write_thru_mem_count);
	fprintf(file1, "%d\t", total_access_time);
	fprintf(file1, "\n");
	fprintf(file1, "\n");

	fclose(file1);
}




int main()
{
	int i, j, k, n = 128, nrot, h = 1, t = 2;
	 uint64_t x[16384];//uint64_t -- 8 bytes
	 file_init();
	 double **a1, **v1, *d;
	 a1 = matrix(1, 128, 1, 128);
	 v1 = matrix(1, 128, 1, 128);
	 d = vector(1, 128);

	//L = 2;
	
	for (strat = 1; strat <= 3; strat++)
	{
		for (BL = 1; BL <= 8; BL *= 2)
		{
			for (N = 1; N <= 16; N *= 2)
			{
				init();
				B = BL*(w / 8);//N bytes
				L = 65536 / (B * N);
				t = 2;
				for (i = 1; i < n + 1; i++)//making it symmetric
				{
					for (j = i; j < n + 1; j++)
					{
						if (i == j)
						{
							a1[i][j] = t++;
						}
						else
						{
							a1[i][j] = i + (2 * j);
							a1[j][i] = i + (2 * j);
						}
					}

				}

				jacobi(a1, n, d, v1, &nrot);
				empty_cac();//clear any dirty remaining in cache and dump it in memory
				
				if (strat == 2)//for write through non-allocate
				{
					total_access_time = ((read_cache_count) * 1) + ((read_dirty_replace_count) * (90 + (BL - 1) * 15)) + (write_thru_mem_count * 90)
						+ ((read_block_time) * (90 + (BL - 1) * 15));// 90ns for write miss/hit+read cache time+ read dirty replace time(not be used) + read from memory into cache +ignoring 1ns of hit because it is in parallel with write_thru_mem_count
				}
				else if (strat == 3)//for write through allocate
				{
					total_access_time = ((read_cache_count) * 1) + ((read_block_time) * (90 + (BL - 1) * 15)) + ((read_dirty_replace_count) * (90 + (BL - 1) * 15))
						+ ((write_thru_mem_count- write_block_time) * 90) + (((write_block_time) * (90 + (BL - 1) * 15)) + ((write_block_time) * 1));//time of read from uP to cache, memory to cache and(90|| 1ns) for write thru and (90 + (BL - 1) * 15)) + 1ns for write miss
						                                                                                     //write_block_time) * 1 is hit time in miss case                                    
				}
				
				else//for writeback
				{
					total_access_time = ((read_cache_count + write_cache_count) * 1) + ((read_dirty_replace_count) * (90 + (BL - 1) * 15)) + ((read_block_time) * (90 + (BL - 1) * 15))
						+ ((write_dirty_replace_count) * (90 + (BL - 1) * 15)) + ((write_block_time) * (90 + (BL - 1) * 15)) + ((flush_count) * (90 + (BL - 1) * 15));
						//read hit and write hit time to cache(1ns)+read dirty replace time + readblock time + write dirty replace time + writeblock time + flush time
				}
				printf("Total Access time = %d", total_access_time);
				file_display();
				}
		}
	}





	return 0;
}


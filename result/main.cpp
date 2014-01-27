#include "result.cpp"
#include <iostream>

#ifdef _MSC_VER
#define _USE_MATH_DEFINES
#include <math.h>
#endif

#include <malloc.h>
#include <cstring>

// AUTOLIB_MEM_ALIGNMENT - alignment used by autolib_malloc.
#define AUTOLIB_MEM_ALIGNMENT   16

/* ---------------------------------------------------
 * Memory management
 * --------------------------------------------------- */

void * autolib_malloc(size_t size) {
#ifdef _MSC_VER
    return _aligned_malloc(size, AUTOLIB_MEM_ALIGNMENT);
#else
    return memalign(AUTOLIB_MEM_ALIGNMENT, size);
#endif
}

void autolib_free(void *ptr) {
#ifdef _MSC_VER
    _aligned_free(ptr);
#else
    free(ptr);
#endif
}


#define VERIFIER_MEM_PATTERN	0xCC

void* autolib_ver_malloc(size_t size, bool unaligned = false) {
    size_t  border_size = ((size + AUTOLIB_MEM_ALIGNMENT - 1)/AUTOLIB_MEM_ALIGNMENT) *AUTOLIB_MEM_ALIGNMENT; 
    if (2*sizeof(size_t ) > border_size )
        border_size = 2*sizeof(size_t );
    if (unaligned)
        border_size++;

    char* result = (char*)autolib_malloc(size + 2*border_size);
    if ( result == NULL )
    	return NULL;

    // fill borders with pattern
    memset(result , VERIFIER_MEM_PATTERN, border_size);
    memset(result + size + border_size , VERIFIER_MEM_PATTERN, border_size);
    // write sizes at both ends
    size_t* ps = (size_t*)(result + border_size - sizeof(size_t ));
    size_t* pe = (size_t*)(result + border_size + size);
    *ps-- = size;
    *pe++ = size;
    *ps = border_size;
    *pe = border_size;
    return result + border_size;
}

bool autolib_ver_free(void* p, const char* name) {
    // figure out buffer and border sizes
    size_t* pe = (size_t*)p;
    size_t buffer_size = *(--pe);
    size_t border_size = *(--pe);
    // check that border_size is not below minimal border size
    if (border_size<2*sizeof(size_t)) {
		std::cout << "! error: " << name << " buffer has invalid border size value\n";
        return false;
    }
    // compare values stored at beginning and at the end of buffer
    pe = (size_t*)((char*)p + buffer_size);
    if (*pe != buffer_size) {
		std::cout << "! error: " << name << " buffer size value at the beginning doesn't match to the size value at the end\n";
        return false;
    }
    pe++;
    if (*pe != border_size) {
		std::cout << "! error: " << name << " buffer prologue and epilogue size don't match\n";
        return false;
    }
    pe++;
    p = ((char*)p - border_size);
    border_size -= 2*sizeof(size_t);
    // check patterns
    unsigned char* t = (unsigned char*)p;
    for (int i=0; i<border_size; i++, t++)
        if (*t != VERIFIER_MEM_PATTERN) {
			std::cout << "! error: " << name << " buffer prologue of size " << border_size << " corrupted at byte " << i << "\n";
            autolib_free(p);
            return false;
        }

    t = (unsigned char*)pe;
    for (int i=0; i<border_size; i++, t++)
        if (*t != VERIFIER_MEM_PATTERN) {
			std::cout << "! error: " << name << " buffer epilogue of size " << border_size << " corrupted at byte " << i << "\n";
            autolib_free(p);
            return false;
        }

    autolib_free(p);
    return true;
}

/* ---------------------------------------------------
 * Vector utilities
 * --------------------------------------------------- */

int autolib_compare_vecs(char *id1, float *v1, char *id2, float *v2, int n, double threshold) {
    int pass = 1;
    int printed = 0;
    const int max_printed = 100;
    for(int i=0; i<n; ++i) {
        float diff = (v1[i] - v2[i]);
        diff = (diff < 0) ? (-diff) : diff;
        if((double)diff > threshold) {
            if(printed++ < max_printed)
				std::cout << "#  (" << id1 << "[" << i << "] - " << id2 << "[" << i << "]) = " << diff
						  << "  me/them  " << v1[i] << "  " << v2[i] << std::endl;
            pass=0;
        }
    }
    return pass;
}

void autolib_impulse_vec(float *Y, int n, int j) {
    for(int i=0; i<n; ++i) Y[i] = (float)0.0;
    Y[j] = (float) 1.0;
}

void autolib_rand_vec(float *Y, int n) {
    for(int i=0; i<n; ++i) Y[i] = ((float)rand()) / ((float)RAND_MAX) * 2.0 - 1.0;
}

void autolib_const_vec(float *Y, int n, float c) {
    for(int i=0; i<n; ++i) Y[i] = c;
}

void autolib_piecewise_vec(float *Y, int n) {
    for(int i=0; i<n; ++i)  Y[i] = (float)i+1;
}

void autolib_verif_print_vec(char *id, float *v, int n) {
	std::cout << "# " << id << ": [";
    for(int i=0; i<n-1; ++i) std::cout << v[i] << ", ";
    if(n>0) std::cout << v[n-1];
	std::cout << "]" << std::endl;
}

void autolib_copy_vec(float *X, float* Y, int n) {
    for(int i=0; i<n; ++i) Y[i] = X[i];
}


class Verifier {
public:
    virtual bool verify(RS1 *lib, double threshold) = 0;
};


class TransformVerifier : public Verifier{
public:
    TransformVerifier() { this->n = 0; }
    TransformVerifier(int n, int num_tests = 100) {
        this->n = n;
        this->num_tests = (num_tests >= n) ? n : num_tests;
    }

    virtual float kernel(int i, int j) = 0;
    virtual int _numX() { return this->n; }
    virtual int _numY() { return this->n; }

    float sample(float *X, int i) {
        float res = 0.0;
        for(int j = 0; j < _numX(); ++j) res += X[j] * kernel(i, j);
        return res;
    }

    void impulse_resp(float *Y, int j) {
        for(int i = 0; i < _numY(); ++i) Y[i] = kernel(i, j);
    }

    bool _verify(float *X, float *Y, RS1 *lib, double threshold) {
        // warning: X might be equal to Y 
        float *Xref = (float*) autolib_ver_malloc(sizeof(float)*_numX());
        float *Yref = (float*) autolib_ver_malloc(sizeof(float)*_numY());
        float *yy = (float*) autolib_ver_malloc(sizeof(float)*num_tests);
        float *yyref = (float*) autolib_ver_malloc(sizeof(float)*num_tests);

		std::cout << "# check impulse response \n";
        for(int k=0; k<num_tests; ++k) {
            int j = rand() % _numX();
            autolib_const_vec(Y, _numY(), (float) 7.7);
            autolib_impulse_vec(X, _numX(), j);
            autolib_copy_vec(X, Xref, _numX());
            { lib->compute(reinterpret_cast<std::complex<float>*>(Y), reinterpret_cast<std::complex<float>*>(X)); }
            impulse_resp(Yref, j);
            if(!autolib_compare_vecs((char*)"Y", Y, (char*)"Yref", Yref, _numY(), threshold)) {
                if(n <= num_tests) {
                    autolib_verif_print_vec((char*)"X   ", Xref, _numX());
                    autolib_verif_print_vec((char*)"Y   ", Y,    _numY());
                    autolib_verif_print_vec((char*)"Yref", Yref, _numY());
                }
                autolib_ver_free(Yref,"Yref");     autolib_ver_free(Xref, "Xref");
                autolib_ver_free(yy, "yy");        autolib_ver_free(yyref, "yyref");
                return false;
            }
        }

		std::cout << "# check several output samples \n";
        autolib_const_vec(Y, _numY(), (float) 0);
        autolib_rand_vec(X, _numX());
        autolib_copy_vec(X, Xref, _numX());
        { lib->compute(reinterpret_cast<std::complex<float>*>(Y), reinterpret_cast<std::complex<float>*>(X)); }
        for(int k=0; k<num_tests; ++k) {
            int i = (_numY()==num_tests) ? k : (rand() % _numY());
            yy[k] = Y[i];
            yyref[k] = sample(Xref, i);
        }
        if(!autolib_compare_vecs((char*)"yy", yy, (char*)"yyref", yyref, num_tests, threshold)) {
            if(_numX() <= num_tests) autolib_verif_print_vec((char*)"X   ", Xref, _numX());
            autolib_verif_print_vec((char*)"yy   ", yy, num_tests);
            autolib_verif_print_vec((char*)"yyref", yyref, num_tests);
            autolib_ver_free(Yref,"Yref");     autolib_ver_free(Xref, "Xref");
            autolib_ver_free(yy, "yy");        autolib_ver_free(yyref, "yyref");
            return false;
        }

        autolib_ver_free(Yref,"Yref");     autolib_ver_free(Xref, "Xref");
        autolib_ver_free(yy, "yy");        autolib_ver_free(yyref, "yyref");
        return true;
    }

    bool verifyEx(RS1 *lib, double threshold, bool inplace = false, bool unaligned = false) {
        float *Y, *X;
        int sizeX = sizeof(float)*_numX();
        int sizeY = sizeof(float)*_numY();
        if (unaligned) return true;
        if (inplace) {
            X = (float*) autolib_ver_malloc((sizeX<sizeY) ? sizeY: sizeX, unaligned);
            Y = X;
        } else {
            X = (float*) autolib_ver_malloc(sizeX, unaligned);
            Y = (float*) autolib_ver_malloc(sizeY, unaligned);
        }
#ifdef VERIFIER_USE_INIT_FUNCTIONS
        if (!lib->init(reinterpret_cast<float*>(Y), reinterpret_cast<float*>(X))) {
			std::cout << "! error: lib init failed\n";
            return false;
        }
#endif
        bool result = _verify(X, Y, lib, threshold);

        if (!autolib_ver_free(X, "X")) return false;
        if (!inplace) 
            if (!autolib_ver_free(Y, "Y")) return false;

        return result;
    }

    bool verify(RS1 *lib, double threshold) {
    	return verifyEx(lib, threshold, false, false);
    }

    int n;
    int num_tests;
};

class libdft_Verifier : public TransformVerifier {
public:
    /* note that 2*n is passed down to Verifier */
    libdft_Verifier(int n, int num_tests=100) : TransformVerifier(2*n, num_tests) {}
    virtual float kernel(int i, int j) {
        int n = this->n / 2;
        double idx = (double)(i/2) * (double)(j/2);

        if((i%2)==0) return (j%2)==0 ? cos(-2*idx*M_PI/n) : -sin(-2*idx*M_PI/n);
        else         return (j%2)==0 ? sin(-2*idx*M_PI/n) :  cos(-2*idx*M_PI/n);
    }
    int rot;
    double scale;
};


int main(int argc, char** argv) {
	if (argc != 2) {
		std::cout << "usage: " <<argv[0] << " n" << std::endl;
	} else {
		try {
			std::cout << "argc: " << argc << std::endl;
			int n = atoi(argv[1]);
			RS1 dft(n);
				
			double threshold = 1e-2;
			Verifier *v = new libdft_Verifier(n);
			if(v->verify(&dft, threshold)) std::cout << "PASS\n";
			else std::cout << "FAIL\n";
			delete v;

		} catch (std::string str) {
			std::cout << "Exception:" << str << std::endl;
		}
	}
}

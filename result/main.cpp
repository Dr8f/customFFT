#include "result.cpp"
#include <iostream>
#include <iomanip>
#include <malloc.h>
#include <cstring>

#define MEMORY_ALIGNMENT   16

#define VERIFIER_MEM_PATTERN	0xCC

void* ver_malloc(size_t size) {
    size_t  border_size = ((size + MEMORY_ALIGNMENT - 1)/MEMORY_ALIGNMENT) *MEMORY_ALIGNMENT; 
    if (2*sizeof(size_t ) > border_size )
        border_size = 2*sizeof(size_t );

    char* result = (char*)memalign(MEMORY_ALIGNMENT, (size + 2*border_size));
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

bool ver_free(void* p, const char* name) {
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
            free(p);
            return false;
        }

    t = (unsigned char*)pe;
    for (int i=0; i<border_size; i++, t++)
        if (*t != VERIFIER_MEM_PATTERN) {
			std::cout << "! error: " << name << " buffer epilogue of size " << border_size << " corrupted at byte " << i << "\n";
            free(p);
            return false;
        }

    free(p);
    return true;
}

/* ---------------------------------------------------
 * Vector utilities
 * --------------------------------------------------- */

int compare_vecs(char *id1, float *v1, char *id2, float *v2, int n, double threshold) {
    int pass = 1;
    int printed = 0;
    const int max_printed = 100;
    for(int i=0; i<n; ++i) {
        float diff = (v1[i] - v2[i]);
        diff = (diff < 0) ? (-diff) : diff;
        if((double)diff > threshold) {
            if(printed++ < max_printed)
	      std::cout << std::fixed << std::setprecision(2) 
			<< "#  (" << id1 << "[" << i << "] - " << id2 << "[" << i << "]) = " << diff
			<< "  me/them  " << v1[i] << "  " << v2[i] << std::endl;
            pass=0;
        }
    }
    return pass;
}

void impulse_vec(float *Y, int n, int j) {
    for(int i=0; i<n; ++i) Y[i] = (float)0.0;
    Y[j] = (float) 1.0;
}

void rand_vec(float *Y, int n) {
    for(int i=0; i<n; ++i) Y[i] = ((float)rand()) / ((float)RAND_MAX) * 2.0 - 1.0;
}

void const_vec(float *Y, int n, float c) {
    for(int i=0; i<n; ++i) Y[i] = c;
}

void piecewise_vec(float *Y, int n) {
    for(int i=0; i<n; ++i)  Y[i] = (float)i+1;
}

void verif_print_vec(char *id, float *v, int n) {
	std::cout << "# " << id << ": [";
    for(int i=0; i<n-1; ++i) std::cout << v[i] << ", ";
    if(n>0) std::cout << v[n-1];
	std::cout << "]" << std::endl;
}

void copy_vec(float *X, float* Y, int n) {
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
        float *Xref = (float*) ver_malloc(sizeof(float)*_numX());
        float *Yref = (float*) ver_malloc(sizeof(float)*_numY());
        float *yy = (float*) ver_malloc(sizeof(float)*num_tests);
        float *yyref = (float*) ver_malloc(sizeof(float)*num_tests);

		std::cout << "# check impulse response \n";
        for(int k=0; k<num_tests; ++k) {
            int j = rand() % _numX();
            const_vec(Y, _numY(), (float) 7.7);
            impulse_vec(X, _numX(), j);
            copy_vec(X, Xref, _numX());
            { lib->compute(reinterpret_cast<std::complex<float>*>(Y), reinterpret_cast<std::complex<float>*>(X)); }
            impulse_resp(Yref, j);
            if(!compare_vecs((char*)"Y", Y, (char*)"Yref", Yref, _numY(), threshold)) {
                if(n <= num_tests) {
                    verif_print_vec((char*)"X   ", Xref, _numX());
                    verif_print_vec((char*)"Y   ", Y,    _numY());
                    verif_print_vec((char*)"Yref", Yref, _numY());
                }
                ver_free(Yref,"Yref");     ver_free(Xref, "Xref");
                ver_free(yy, "yy");        ver_free(yyref, "yyref");
                return false;
            }
        }

		std::cout << "# check several output samples \n";
        const_vec(Y, _numY(), (float) 0);
        rand_vec(X, _numX());
        copy_vec(X, Xref, _numX());
        { lib->compute(reinterpret_cast<std::complex<float>*>(Y), reinterpret_cast<std::complex<float>*>(X)); }
        for(int k=0; k<num_tests; ++k) {
            int i = (_numY()==num_tests) ? k : (rand() % _numY());
            yy[k] = Y[i];
            yyref[k] = sample(Xref, i);
        }
        if(!compare_vecs((char*)"yy", yy, (char*)"yyref", yyref, num_tests, threshold)) {
            if(_numX() <= num_tests) verif_print_vec((char*)"X   ", Xref, _numX());
            verif_print_vec((char*)"yy   ", yy, num_tests);
            verif_print_vec((char*)"yyref", yyref, num_tests);
            ver_free(Yref,"Yref");     ver_free(Xref, "Xref");
            ver_free(yy, "yy");        ver_free(yyref, "yyref");
            return false;
        }

        ver_free(Yref,"Yref");     ver_free(Xref, "Xref");
        ver_free(yy, "yy");        ver_free(yyref, "yyref");
        return true;
    }

    bool verify(RS1 *lib, double threshold) {
		float* X = (float*) ver_malloc(sizeof(float)*this->n);
		float* Y = (float*) ver_malloc(sizeof(float)*this->n);
        bool result = _verify(X, Y, lib, threshold);
        if (!ver_free(X, "X")) return false;
		if (!ver_free(Y, "Y")) return false;
        return result;
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

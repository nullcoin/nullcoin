#ifndef SCRYPT_H
#define SCRYPT_H


class Scrypt
{
public:
    Scrypt(unsigned int nBits);
    ~Scrypt();

    void CleanUp();
    void Reset(unsigned int nBits);
    void Target_2_1(const char *input, char *output);

protected:
    unsigned int    m_TargetR;
    void*           m_B0;
    void*           m_V0;
    void*           m_XY0;
};



#endif

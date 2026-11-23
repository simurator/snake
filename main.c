#define _WIN32_WINNT 0x0601
#include <windows.h>
#include <stdint.h>
#include <stdlib.h>
#include <time.h>
#include <math.h>
#include <stdio.h>
#include <string.h>

// ===== KONFIG =====
#define WIN_W 900
#define WIN_H 640
#define GRID_W 30
#define GRID_H 20
#define KOM 24
#define BOARD_X 40
#define BOARD_Y 50
#define MAX_DLUGOSC (GRID_W * GRID_H)

// ===== SIEĆ =====
#define WEJSCIA 11
#define UKRYTA1 128
#define UKRYTA2 128
#define WYJSCIA 3
#define LR 0.001f
#define GAMMA 0.95f
#define BATCH 64
#define REPLAY 50000
#define TARGET_SYNC 500
#define EPIZODY_TRENINGU 300
#define MAX_WATKOW 32

// ===== TYPY =====
typedef struct { int x, y; } Punkt;

typedef struct {
    Punkt cialo[MAX_DLUGOSC];
    int dlugosc;
    int kierunek;
    int nastepny_kierunek;
} Waz;

typedef struct {
    float x, y, vx, vy, zycie;
    int kolor;
    float rozmiar;
} Czasteczka;

typedef struct {
    float W1[UKRYTA1][WEJSCIA];
    float b1[UKRYTA1];
    float W2[UKRYTA2][UKRYTA1];
    float b2[UKRYTA2];
    float W3[WYJSCIA][UKRYTA2];
    float b3[WYJSCIA];
} Siec;

typedef struct {
    float mW1[UKRYTA1][WEJSCIA], vW1[UKRYTA1][WEJSCIA];
    float mb1[UKRYTA1], vb1[UKRYTA1];
    float mW2[UKRYTA2][UKRYTA1], vW2[UKRYTA2][UKRYTA1];
    float mb2[UKRYTA2], vb2[UKRYTA2];
    float mW3[WYJSCIA][UKRYTA2], vW3[WYJSCIA][UKRYTA2];
    float mb3[WYJSCIA], vb3[WYJSCIA];
    int t;
} Adam;

typedef struct {
    float stan[WEJSCIA];
    int akcja;
    float nagroda;
    float nastepnyStan[WEJSCIA];
    int koniec;
} Doswiadczenie;

typedef struct {
    float gW1[UKRYTA1][WEJSCIA]; float gb1[UKRYTA1];
    float gW2[UKRYTA2][UKRYTA1]; float gb2[UKRYTA2];
    float gW3[WYJSCIA][UKRYTA2]; float gb3[WYJSCIA];
    int liczbaProbek;
} Gradienty;

// ===== GLOBALE =====
static uint32_t *PIXELE = NULL;
static BITMAPINFO bmi;

static Waz waz;
static Punkt jedzenie;
static Czasteczka czasteczki[128];

static int punkty = 0;
static int rekord = 0;
static int predkoscMs = 100;
static int tryb = 0;
static int pauza = 0;
static int koniecGry = 0;
static float czasAnim = 0.0f;
static float akumulatorRuchu = 0.0f;

static Siec siec;
static Siec siecTarget;
static Adam adam;

static Doswiadczenie replay[REPLAY];
static int replayIdx = 0;
static int replayFill = 0;
static CRITICAL_SECTION csReplay;
static CRITICAL_SECTION csSiec;

static int trenEpizod = 0;
static int trenBest = 0;
static long long trenSuma = 0;
static int trenCalkowity = 0;
static int krokiGlobalne = 0;

// ===== WĄTKI =====
static int liczbaWatkow = 1;
static HANDLE *watki = NULL;
static Gradienty *gradientyWatkow = NULL;
static HANDLE *eventyStart = NULL;   // po jednym na watek
static HANDLE *eventyDone = NULL;    // po jednym na watek
static volatile LONG watekStop = 0;
static volatile LONG watekRoboty = 0;

static Doswiadczenie *batchPtr[BATCH];
static volatile LONG batchRozmiar = 0;
static volatile LONG indeksNastepny = 0;

static int myszX = 0, myszY = 0;

// ===== KONSOLA =====
static HANDLE hKonsola = NULL;
static int konsolaGotowa = 0;
static double ostatniCzasKonsoli = 0.0;
static int ostatniEpKonsoli = -1;

// ===== KOLORY =====
#define K_TLO       0x00121820
#define K_GLOWA1    0x0080FF80
#define K_GLOWA2    0x0030C040
#define K_CIALO1    0x0040E050
#define K_CIALO2    0x00208030
#define K_JEDZ1     0x00FF4060
#define K_JEDZ2     0x00FFA0B0
#define K_CIEN      0x00000000
#define K_HUD       0x00E0E0F0
#define K_HUD2      0x008090A0
#define K_AI        0x0060C0FF
#define K_RAMKA     0x00406080
#define K_ZLOTO     0x00FFD040

// ===== BUFOR PIKSELI =====
static inline void piksel(int x, int y, uint32_t kolor, float alpha) {
    if (x < 0 || x >= WIN_W || y < 0 || y >= WIN_H) return;
    if (alpha <= 0.0f) return;
    if (alpha >= 1.0f) { PIXELE[y * WIN_W + x] = kolor; return; }
    uint32_t dst = PIXELE[y * WIN_W + x];
    int dr = (dst >> 16) & 0xFF, dg = (dst >> 8) & 0xFF, db = dst & 0xFF;
    int sr = (kolor >> 16) & 0xFF, sg = (kolor >> 8) & 0xFF, sb = kolor & 0xFF;
    int r = (int)(sr * alpha + dr * (1 - alpha));
    int g = (int)(sg * alpha + dg * (1 - alpha));
    int b = (int)(sb * alpha + db * (1 - alpha));
    PIXELE[y * WIN_W + x] = (r << 16) | (g << 8) | b;
}

static void wypelnijProst(int x0, int y0, int x1, int y1, uint32_t kolor, float a) {
    if (x0 < 0) x0 = 0;
    if (y0 < 0) y0 = 0;
    if (x1 > WIN_W) x1 = WIN_W;
    if (y1 > WIN_H) y1 = WIN_H;
    for (int y = y0; y < y1; y++)
        for (int x = x0; x < x1; x++)
            piksel(x, y, kolor, a);
}

static void wypelnijKolo(int cx, int cy, int r, uint32_t kolor, float a) {
    if (r <= 0) return;
    int r2 = r * r;
    for (int y = -r; y <= r; y++) {
        for (int x = -r; x <= r; x++) {
            int d2 = x*x + y*y;
            if (d2 <= r2) {
                float aa = 1.0f;
                if (d2 > r2 - r) aa = (float)(r2 - d2) / (float)r;
                if (aa > 1.0f) aa = 1.0f;
                if (aa < 0.0f) aa = 0.0f;
                piksel(cx + x, cy + y, kolor, a * aa);
            }
        }
    }
}

// ===== CZCIONKA =====
// indeksy: 0 spacja, 1-10 cyfry, 11-36 litery, 37 '.', 38 '%', 39 '/', 40 '|', 41 '-', 42 ':'
static const uint8_t FONT5x7[][5] = {
    {0x00,0x00,0x00,0x00,0x00},{0x3E,0x51,0x49,0x45,0x3E},{0x00,0x42,0x7F,0x40,0x00},
    {0x42,0x61,0x51,0x49,0x46},{0x21,0x41,0x45,0x4B,0x31},{0x18,0x14,0x12,0x7F,0x10},
    {0x27,0x45,0x45,0x45,0x39},{0x3C,0x4A,0x49,0x49,0x30},{0x01,0x71,0x09,0x05,0x03},
    {0x36,0x49,0x49,0x49,0x36},{0x06,0x49,0x49,0x29,0x1E},{0x7E,0x11,0x11,0x11,0x7E},
    {0x7F,0x49,0x49,0x49,0x36},{0x3E,0x41,0x41,0x41,0x22},{0x7F,0x41,0x41,0x22,0x1C},
    {0x7F,0x49,0x49,0x49,0x41},{0x7F,0x09,0x09,0x09,0x01},{0x3E,0x41,0x49,0x49,0x7A},
    {0x7F,0x08,0x08,0x08,0x7F},{0x00,0x41,0x7F,0x41,0x00},{0x20,0x40,0x41,0x3F,0x01},
    {0x7F,0x08,0x14,0x22,0x41},{0x7F,0x40,0x40,0x40,0x40},{0x7F,0x02,0x0C,0x02,0x7F},
    {0x7F,0x04,0x08,0x10,0x7F},{0x3E,0x41,0x41,0x41,0x3E},{0x7F,0x09,0x09,0x09,0x06},
    {0x3E,0x41,0x51,0x21,0x5E},{0x7F,0x09,0x19,0x29,0x46},{0x46,0x49,0x49,0x49,0x31},
    {0x01,0x01,0x7F,0x01,0x01},{0x3F,0x40,0x40,0x40,0x3F},{0x1F,0x20,0x40,0x20,0x1F},
    {0x3F,0x40,0x38,0x40,0x3F},{0x63,0x14,0x08,0x14,0x63},{0x07,0x08,0x70,0x08,0x07},
    {0x61,0x51,0x49,0x45,0x43},
    {0x00,0x60,0x60,0x00,0x00},   // 37 '.'
    {0x23,0x13,0x08,0x64,0x62},   // 38 '%'
    {0x20,0x10,0x08,0x04,0x02},   // 39 '/'
    {0x00,0x00,0x7F,0x00,0x00},   // 40 '|'
    {0x08,0x08,0x08,0x08,0x08},   // 41 '-'
    {0x00,0x36,0x36,0x00,0x00},   // 42 ':'
};

static void rysujZnak(int cx, int cy, char c, uint32_t kolor, int skala) {
    if (c >= 'a' && c <= 'z') c -= 32;
    int idx = -1;
    if (c == ' ') idx = 0;
    else if (c >= '0' && c <= '9') idx = c - '0' + 1;
    else if (c >= 'A' && c <= 'Z') idx = c - 'A' + 11;
    else if (c == '.') idx = 37;
    else if (c == '%') idx = 38;
    else if (c == '/') idx = 39;
    else if (c == '|') idx = 40;
    else if (c == '-') idx = 41;
    else if (c == ':') idx = 42;
    if (idx < 0) return;
    for (int col = 0; col < 5; col++) {
        uint8_t b = FONT5x7[idx][col];
        for (int row = 0; row < 7; row++) {
            if (b & (1 << row))
                wypelnijProst(cx + col*skala, cy + row*skala,
                              cx + col*skala + skala, cy + row*skala + skala, kolor, 1.0f);
        }
    }
}

static void rysujText(int x, int y, const char *s, uint32_t kolor, int skala) {
    while (*s) { rysujZnak(x, y, *s, kolor, skala); x += 6 * skala; s++; }
}

static int dlugoscText(const char *s, int skala) {
    int n = 0; while (*s++) n++;
    return n * 6 * skala;
}

// ===== SIEĆ =====
static void inicjujSiec(Siec *s) {
    for (int i = 0; i < UKRYTA1; i++) {
        for (int j = 0; j < WEJSCIA; j++)
            s->W1[i][j] = ((float)rand()/RAND_MAX - 0.5f) * sqrtf(2.0f / WEJSCIA);
        s->b1[i] = 0.0f;
    }
    for (int i = 0; i < UKRYTA2; i++) {
        for (int j = 0; j < UKRYTA1; j++)
            s->W2[i][j] = ((float)rand()/RAND_MAX - 0.5f) * sqrtf(2.0f / UKRYTA1);
        s->b2[i] = 0.0f;
    }
    for (int i = 0; i < WYJSCIA; i++) {
        for (int j = 0; j < UKRYTA2; j++)
            s->W3[i][j] = ((float)rand()/RAND_MAX - 0.5f) * sqrtf(2.0f / UKRYTA2);
        s->b3[i] = 0.0f;
    }
}

static void kopiujSiec(Siec *dst, Siec *src) { memcpy(dst, src, sizeof(Siec)); }
static void zerujAdam(void) { memset(&adam, 0, sizeof(adam)); }

static void forward(Siec *s, const float *wej, float *h1, float *h2, float *wyj) {
    for (int i = 0; i < UKRYTA1; i++) {
        float sum = s->b1[i];
        for (int j = 0; j < WEJSCIA; j++) sum += s->W1[i][j] * wej[j];
        h1[i] = sum > 0.0f ? sum : 0.0f;
    }
    for (int i = 0; i < UKRYTA2; i++) {
        float sum = s->b2[i];
        for (int j = 0; j < UKRYTA1; j++) sum += s->W2[i][j] * h1[j];
        h2[i] = sum > 0.0f ? sum : 0.0f;
    }
    for (int i = 0; i < WYJSCIA; i++) {
        float sum = s->b3[i];
        for (int j = 0; j < UKRYTA2; j++) sum += s->W3[i][j] * h2[j];
        wyj[i] = sum;
    }
}

// ===== WĄTEK ROBOCZY =====
static DWORD WINAPI watekRoboczy(LPVOID arg) {
    int id = (int)(intptr_t)arg;
    Gradienty *g = &gradientyWatkow[id];
    float h1[UKRYTA1], h2[UKRYTA2], wyj[WYJSCIA];
    float th1[UKRYTA1], th2[UKRYTA2], twyj[WYJSCIA];
    float d1[UKRYTA1], d2[UKRYTA2], d3[WYJSCIA];

    while (!watekStop) {
        WaitForSingleObject(eventyStart[id], INFINITE);
        if (watekStop) break;

        memset(g, 0, sizeof(*g));
        int licznik = 0;

        while (1) {
            LONG idx = InterlockedIncrement(&indeksNastepny) - 1;
            if (idx >= batchRozmiar) break;

            Doswiadczenie *d = batchPtr[idx];
            if (!d) continue;

            forward(&siec, d->stan, h1, h2, wyj);

            float targetQ;
            if (d->koniec) {
                targetQ = d->nagroda;
            } else {
                forward(&siecTarget, d->nastepnyStan, th1, th2, twyj);
                float maxNext = twyj[0];
                for (int i = 1; i < WYJSCIA; i++) if (twyj[i] > maxNext) maxNext = twyj[i];
                targetQ = d->nagroda + GAMMA * maxNext;
            }

            float err = wyj[d->akcja] - targetQ;
            float huberGrad = (fabsf(err) <= 1.0f) ? err : (err > 0 ? 1.0f : -1.0f);

            for (int i = 0; i < WYJSCIA; i++) d3[i] = (i == d->akcja) ? huberGrad : 0.0f;

            for (int i = 0; i < WYJSCIA; i++) {
                g->gb3[i] += d3[i];
                for (int j = 0; j < UKRYTA2; j++) g->gW3[i][j] += d3[i] * h2[j];
            }

            for (int j = 0; j < UKRYTA2; j++) {
                float s = 0.0f;
                for (int i = 0; i < WYJSCIA; i++) s += d3[i] * siec.W3[i][j];
                d2[j] = (h2[j] > 0.0f) ? s : 0.0f;
            }
            for (int i = 0; i < UKRYTA2; i++) {
                g->gb2[i] += d2[i];
                for (int j = 0; j < UKRYTA1; j++) g->gW2[i][j] += d2[i] * h1[j];
            }

            for (int j = 0; j < UKRYTA1; j++) {
                float s = 0.0f;
                for (int i = 0; i < UKRYTA2; i++) s += d2[i] * siec.W2[i][j];
                d1[j] = (h1[j] > 0.0f) ? s : 0.0f;
            }
            for (int i = 0; i < UKRYTA1; i++) {
                g->gb1[i] += d1[i];
                for (int j = 0; j < WEJSCIA; j++) g->gW1[i][j] += d1[i] * d->stan[j];
            }

            licznik++;
        }
        g->liczbaProbek = licznik;

        InterlockedIncrement(&watekRoboty);
        SetEvent(eventyDone[id]);
    }
    return 0;
}

// ===== ADAM =====
static void adamUpdate(float *param, float *grad, float *m, float *v, float lr) {
    const float beta1 = 0.9f, beta2 = 0.999f, eps = 1e-8f;
    *m = beta1 * (*m) + (1 - beta1) * (*grad);
    *v = beta2 * (*v) + (1 - beta2) * (*grad) * (*grad);
    float mHat = *m / (1.0f - powf(beta1, (float)adam.t));
    float vHat = *v / (1.0f - powf(beta2, (float)adam.t));
    *param -= lr * mHat / (sqrtf(vHat) + eps);
}

// ===== RÓWNOLEGŁY BATCH =====
static void trenujBatchRownolegle(void) {
    if (replayFill < BATCH) return;

    EnterCriticalSection(&csSiec);
    for (int i = 0; i < BATCH; i++) {
        int idx = rand() % replayFill;
        batchPtr[i] = &replay[idx];
    }
    adam.t++;

    InterlockedExchange(&indeksNastepny, 0);
    batchRozmiar = BATCH;
    InterlockedExchange(&watekRoboty, 0);

    for (int i = 0; i < liczbaWatkow; i++) SetEvent(eventyStart[i]);
    WaitForMultipleObjects(liczbaWatkow, eventyDone, TRUE, INFINITE);

    float inv = 1.0f / BATCH;
    for (int i = 0; i < UKRYTA1; i++) {
        float accW[WEJSCIA];
        for (int j = 0; j < WEJSCIA; j++) {
            accW[j] = 0;
            for (int w = 0; w < liczbaWatkow; w++) accW[j] += gradientyWatkow[w].gW1[i][j];
        }
        float accB = 0;
        for (int w = 0; w < liczbaWatkow; w++) accB += gradientyWatkow[w].gb1[i];
        for (int j = 0; j < WEJSCIA; j++)
            adamUpdate(&siec.W1[i][j], &(float){accW[j] * inv},
                       &adam.mW1[i][j], &adam.vW1[i][j], LR);
        adamUpdate(&siec.b1[i], &(float){accB * inv},
                   &adam.mb1[i], &adam.vb1[i], LR);
    }
    for (int i = 0; i < UKRYTA2; i++) {
        float accW[UKRYTA1];
        for (int j = 0; j < UKRYTA1; j++) {
            accW[j] = 0;
            for (int w = 0; w < liczbaWatkow; w++) accW[j] += gradientyWatkow[w].gW2[i][j];
        }
        float accB = 0;
        for (int w = 0; w < liczbaWatkow; w++) accB += gradientyWatkow[w].gb2[i];
        for (int j = 0; j < UKRYTA1; j++)
            adamUpdate(&siec.W2[i][j], &(float){accW[j] * inv},
                       &adam.mW2[i][j], &adam.vW2[i][j], LR);
        adamUpdate(&siec.b2[i], &(float){accB * inv},
                   &adam.mb2[i], &adam.vb2[i], LR);
    }
    for (int i = 0; i < WYJSCIA; i++) {
        float accW[UKRYTA2];
        for (int j = 0; j < UKRYTA2; j++) {
            accW[j] = 0;
            for (int w = 0; w < liczbaWatkow; w++) accW[j] += gradientyWatkow[w].gW3[i][j];
        }
        float accB = 0;
        for (int w = 0; w < liczbaWatkow; w++) accB += gradientyWatkow[w].gb3[i];
        for (int j = 0; j < UKRYTA2; j++)
            adamUpdate(&siec.W3[i][j], &(float){accW[j] * inv},
                       &adam.mW3[i][j], &adam.vW3[i][j], LR);
        adamUpdate(&siec.b3[i], &(float){accB * inv},
                   &adam.mb3[i], &adam.vb3[i], LR);
    }

    LeaveCriticalSection(&csSiec);
}

// ===== STAN =====
static int kierDoDx(int k) { return (k==1)?1:(k==3)?-1:0; }
static int kierDoDy(int k) { return (k==2)?1:(k==0)?-1:0; }

static int czySmierc(int x, int y) {
    if (x < 0 || x >= GRID_W || y < 0 || y >= GRID_H) return 1;
    for (int i = 0; i < waz.dlugosc - 1; i++)
        if (waz.cialo[i].x == x && waz.cialo[i].y == y) return 1;
    return 0;
}

static void pobierzStan(float *s) {
    int k = waz.kierunek;
    int hx = waz.cialo[0].x, hy = waz.cialo[0].y;
    int dxF = kierDoDx(k), dyF = kierDoDy(k);
    int kR = (k + 1) % 4, kL = (k + 3) % 4;
    memset(s, 0, sizeof(float) * WEJSCIA);
    s[0] = czySmierc(hx + dxF, hy + dyF) ? 1.0f : 0.0f;
    s[1] = czySmierc(hx + kierDoDx(kR), hy + kierDoDy(kR)) ? 1.0f : 0.0f;
    s[2] = czySmierc(hx + kierDoDx(kL), hy + kierDoDy(kL)) ? 1.0f : 0.0f;
    s[3 + k] = 1.0f;
    if (jedzenie.x < hx) s[7] = 1.0f;
    if (jedzenie.x > hx) s[8] = 1.0f;
    if (jedzenie.y < hy) s[9] = 1.0f;
    if (jedzenie.y > hy) s[10] = 1.0f;
}

static int wybierzAkcje(float *stan, float eps) {
    if ((float)rand() / RAND_MAX < eps) return rand() % WYJSCIA;
    float h1[UKRYTA1], h2[UKRYTA2], wyj[WYJSCIA];
    EnterCriticalSection(&csSiec);
    forward(&siec, stan, h1, h2, wyj);
    LeaveCriticalSection(&csSiec);
    int a = 0; float best = wyj[0];
    for (int i = 1; i < WYJSCIA; i++) if (wyj[i] > best) { best = wyj[i]; a = i; }
    return a;
}

static int akcjaNaKierunek(int k, int a) {
    if (a == 0) return k;
    if (a == 1) return (k + 1) % 4;
    return (k + 3) % 4;
}

// ===== ZAPIS/ODCZYT =====
static void zapiszModel(void) {
    EnterCriticalSection(&csSiec);
    FILE *f = fopen("dqn.bin", "wb");
    if (f) { fwrite(&siec, sizeof(Siec), 1, f); fclose(f); }
    LeaveCriticalSection(&csSiec);
}

static void wczytajModel(void) {
    FILE *f = fopen("dqn.bin", "rb");
    if (f) {
        size_t r = fread(&siec, sizeof(Siec), 1, f);
        fclose(f);
        if (r != 1) inicjujSiec(&siec);
    } else {
        inicjujSiec(&siec);
    }
    kopiujSiec(&siecTarget, &siec);
    zerujAdam();
}

static void wczytajRekord(void) {
    FILE *f = fopen("best.txt", "r");
    if (f) { fscanf(f, "%d", &rekord); fclose(f); }
}
static void zapiszRekord(void) {
    FILE *f = fopen("best.txt", "w");
    if (f) { fprintf(f, "%d", rekord); fclose(f); }
}

// ===== LOGIKA GRY =====
static void generujJedzenie(void) {
    int kolizja;
    do {
        kolizja = 0;
        jedzenie.x = rand() % GRID_W;
        jedzenie.y = rand() % GRID_H;
        for (int i = 0; i < waz.dlugosc; i++)
            if (waz.cialo[i].x == jedzenie.x && waz.cialo[i].y == jedzenie.y) { kolizja = 1; break; }
    } while (kolizja);
}

static void inicjalizujWaza(void) {
    waz.dlugosc = 3;
    waz.kierunek = 1;
    waz.nastepny_kierunek = 1;
    int sx = GRID_W / 2, sy = GRID_H / 2;
    waz.cialo[0] = (Punkt){ sx, sy };
    waz.cialo[1] = (Punkt){ sx - 1, sy };
    waz.cialo[2] = (Punkt){ sx - 2, sy };
}

static void restart(void) {
    inicjalizujWaza();
    generujJedzenie();
    punkty = 0;
    predkoscMs = 100;
    koniecGry = 0;
    pauza = 0;
    for (int i = 0; i < 128; i++) czasteczki[i].zycie = 0;
    akumulatorRuchu = 0;
}

// ===== CZASTECZKI =====
static void dodajCzast(float x, float y, int n, int kolor, float roz) {
    for (int i = 0; i < 128 && n > 0; i++) {
        if (czasteczki[i].zycie <= 0) {
            float ang = (float)rand() / RAND_MAX * 6.2831f;
            float sp = 30.0f + (float)rand() / RAND_MAX * 120.0f;
            czasteczki[i].x = x;
            czasteczki[i].y = y;
            czasteczki[i].vx = cosf(ang) * sp;
            czasteczki[i].vy = sinf(ang) * sp;
            czasteczki[i].zycie = 1.0f;
            czasteczki[i].kolor = kolor;
            czasteczki[i].rozmiar = roz;
            n--;
        }
    }
}

static void aktualizujCzast(float dt) {
    for (int i = 0; i < 128; i++) {
        if (czasteczki[i].zycie > 0) {
            czasteczki[i].x += czasteczki[i].vx * dt;
            czasteczki[i].y += czasteczki[i].vy * dt;
            czasteczki[i].vy += 200.0f * dt;
            czasteczki[i].vx *= 0.98f;
            czasteczki[i].zycie -= dt * 1.6f;
        }
    }
}

// ===== RYSOWANIE =====
static void rysujPlanszeDoBufora(void) {
    for (int y = 0; y < WIN_H; y++) {
        for (int x = 0; x < WIN_W; x++) {
            int ch = ((x / 32) + (y / 32)) & 1;
            uint32_t kolor = ch ? 0x00101820 : 0x00182030;
            float dx = (x - WIN_W/2.0f) / (WIN_W/2.0f);
            float dy = (y - WIN_H/2.0f) / (WIN_H/2.0f);
            float d = dx*dx + dy*dy;
            float a = 0.0f;
            if (d > 0.6f) a = (d - 0.6f) * 0.7f;
            if (a > 0.5f) a = 0.5f;
            piksel(x, y, kolor, 1.0f);
            if (a > 0) piksel(x, y, 0x000000, a);
        }
    }
    wypelnijProst(BOARD_X-4, BOARD_Y-4,
                  BOARD_X + GRID_W*KOM + 4,
                  BOARD_Y + GRID_H*KOM + 4,
                  K_RAMKA, 1.0f);
    wypelnijProst(BOARD_X-2, BOARD_Y-2,
                  BOARD_X + GRID_W*KOM + 2,
                  BOARD_Y + GRID_H*KOM + 2,
                  0x00202830, 1.0f);
    for (int gy = 0; gy < GRID_H; gy++) {
        for (int gx = 0; gx < GRID_W; gx++) {
            if (((gx + gy) & 1) == 0) {
                wypelnijProst(BOARD_X + gx*KOM, BOARD_Y + gy*KOM,
                              BOARD_X + (gx+1)*KOM, BOARD_Y + (gy+1)*KOM,
                              0x001C242C, 1.0f);
            }
        }
    }
}

static void rysujWazDoBufora(void) {
    for (int i = waz.dlugosc - 1; i >= 0; i--) {
        int cx = BOARD_X + waz.cialo[i].x * KOM + KOM/2;
        int cy = BOARD_Y + waz.cialo[i].y * KOM + KOM/2;
        float t = (float)i / (float)(waz.dlugosc > 1 ? waz.dlugosc - 1 : 1);
        uint32_t k1 = K_CIALO1, k2 = K_CIALO2;
        if (i == 0) { k1 = (tryb == 1) ? K_AI : K_GLOWA1; k2 = K_GLOWA2; }
        int r1 = (k1>>16)&0xFF, g1 = (k1>>8)&0xFF, b1 = k1&0xFF;
        int r2 = (k2>>16)&0xFF, g2 = (k2>>8)&0xFF, b2 = k2&0xFF;
        int rr = (int)(r1*(1-t) + r2*t);
        int gg = (int)(g1*(1-t) + g2*t);
        int bb = (int)(b1*(1-t) + b2*t);
        uint32_t kolor = (rr<<16) | (gg<<8) | bb;
        int promien = KOM/2 - 2;
        if (i == 0) promien += 1;
        wypelnijKolo(cx+2, cy+3, promien, K_CIEN, 0.35f);
        wypelnijKolo(cx, cy, promien, kolor, 1.0f);
        wypelnijKolo(cx - promien/3, cy - promien/3, promien/3, 0xFFFFFF, 0.35f);
        if (i == 0) {
            int dx = 0, dy = 0;
            switch (waz.kierunek) {
                case 0: dy = -1; break;
                case 1: dx = 1; break;
                case 2: dy = 1; break;
                case 3: dx = -1; break;
            }
            int ex = cx + dx * 4, ey = cy + dy * 4;
            int px = dy, py = dx;
            wypelnijKolo(ex + px*3, ey + py*3, 2, 0xFFFFFF, 1.0f);
            wypelnijKolo(ex - px*3, ey - py*3, 2, 0xFFFFFF, 1.0f);
            wypelnijKolo(ex + px*3 + dx, ey + py*3 + dy, 1, 0x000000, 1.0f);
            wypelnijKolo(ex - px*3 + dx, ey - py*3 + dy, 1, 0x000000, 1.0f);
        }
    }
}

static void rysujJedzenieDoBufora(void) {
    int cx = BOARD_X + jedzenie.x * KOM + KOM/2;
    int cy = BOARD_Y + jedzenie.y * KOM + KOM/2;
    float puls = 0.5f + 0.5f * sinf(czasAnim * 4.0f);
    int r = (int)(KOM/2 - 2 + puls * 2);
    for (int i = r+6; i > r; i--) {
        float a = 0.06f * (i - r) / 6.0f;
        wypelnijKolo(cx, cy, i, K_JEDZ1, a);
    }
    wypelnijKolo(cx+1, cy+2, r, K_CIEN, 0.4f);
    wypelnijKolo(cx, cy, r, K_JEDZ1, 1.0f);
    wypelnijKolo(cx-2, cy-2, r/3, K_JEDZ2, 0.7f);
}

static void rysujCzastDoBufora(void) {
    for (int i = 0; i < 128; i++) {
        if (czasteczki[i].zycie > 0) {
            float a = czasteczki[i].zycie;
            if (a > 1) a = 1;
            int r = (int)(czasteczki[i].rozmiar * a) + 1;
            wypelnijKolo((int)czasteczki[i].x, (int)czasteczki[i].y,
                         r, czasteczki[i].kolor, a);
        }
    }
}

// ===== EKRAN TRENINGU =====
static void rysujEkranTreningu(HDC hdc, float eps, double sekundy) {
    char buf[160];

    rysujPlanszeDoBufora();
    rysujJedzenieDoBufora();
    rysujWazDoBufora();
    rysujCzastDoBufora();

    wypelnijProst(0, 0, WIN_W, 70, 0x00081018, 0.92f);
    wypelnijProst(0, 70, WIN_W, 72, 0x00406080, 1.0f);

    rysujText(15, 12, "DQN TRENING", K_AI, 2);
    sprintf(buf, "%d watkow (auto) | 11-128-128-3", liczbaWatkow);
    rysujText(15, 42, buf, K_HUD2, 1);

    rysujText(230, 12, "EPIZOD", K_HUD2, 1);
    sprintf(buf, "%d / %d", trenEpizod, trenCalkowity);
    rysujText(230, 30, buf, K_HUD, 2);

    sprintf(buf, "BEST %d", trenBest > rekord ? trenBest : rekord);
    rysujText(460, 12, buf, K_ZLOTO, 2);
    sprintf(buf, "AVG %lld", trenSuma / (trenEpizod ? trenEpizod : 1));
    rysujText(460, 42, buf, K_HUD2, 1);

    sprintf(buf, "EPS %.3f", eps);
    rysujText(630, 12, buf, K_HUD2, 2);
    sprintf(buf, "KROKI %d", krokiGlobalne);
    rysujText(630, 42, buf, K_HUD2, 1);

    int panelY = WIN_H - 40;
    wypelnijProst(0, panelY, WIN_W, WIN_H, 0x00081018, 0.92f);
    wypelnijProst(0, panelY, WIN_W, panelY + 2, 0x00406080, 1.0f);

    int pbarX = 15, pbarY = panelY + 12, pbarW = WIN_W - 30, pbarH = 14;
    wypelnijProst(pbarX, pbarY, pbarX + pbarW, pbarY + pbarH, 0x00202830, 1.0f);
    int pw = (int)(pbarW * ((float)trenEpizod / (float)trenCalkowity));
    wypelnijProst(pbarX, pbarY, pbarX + pw, pbarY + pbarH, K_AI, 1.0f);
    wypelnijProst(pbarX, pbarY, pbarX + pw, pbarY + 3, 0x00A0E0FF, 1.0f);

    float procent = 100.0f * trenEpizod / (float)trenCalkowity;
    double eta = 0.0;
    if (trenEpizod > 0) {
        double srCzas = sekundy / trenEpizod;
        eta = srCzas * (trenCalkowity - trenEpizod);
    }
    sprintf(buf, "%.1f%%  ETA %.0fs  %.1f ep/s", procent, eta,
            trenEpizod > 0 ? (float)trenEpizod / (float)sekundy : 0.0f);
    int tw = dlugoscText(buf, 1);
    rysujText((WIN_W - tw) / 2, panelY + 14, buf, K_HUD, 1);

    StretchDIBits(hdc, 0, 0, WIN_W, WIN_H,
                  0, 0, WIN_W, WIN_H,
                  PIXELE, &bmi, DIB_RGB_COLORS, SRCCOPY);
}

// ===== KONSOLA - POSTĘP =====
static void inicjujKonsole(void) {
    if (!AllocConsole()) return;
    freopen("CONOUT$", "w", stdout);
    hKonsola = GetStdHandle(STD_OUTPUT_HANDLE);

    SetConsoleTitle("DQN Trening - postep");
    SMALL_RECT okno = {0, 0, 79, 14};
    SetConsoleWindowInfo(hKonsola, TRUE, &okno);
    COORD bufor = {80, 300};
    SetConsoleScreenBufferSize(hKonsola, bufor);

    CONSOLE_CURSOR_INFO ci;
    GetConsoleCursorInfo(hKonsola, &ci);
    ci.bVisible = FALSE;
    SetConsoleCursorInfo(hKonsola, &ci);

    system("cls");
    konsolaGotowa = 1;
}

static void rysujPostepKonsoli(float eps, double sekundy) {
    if (!konsolaGotowa) return;

    // odświeżaj max 10 Hz
    if (sekundy - ostatniCzasKonsoli < 0.1 && trenEpizod == ostatniEpKonsoli) return;
    ostatniCzasKonsoli = sekundy;
    ostatniEpKonsoli = trenEpizod;

    char buf[256];
    COORD pos = {0, 0};
    SetConsoleCursorPosition(hKonsola, pos);

    SetConsoleTextAttribute(hKonsola, FOREGROUND_GREEN | FOREGROUND_INTENSITY);
    printf("==============================================================\n");
    SetConsoleTextAttribute(hKonsola, FOREGROUND_RED | FOREGROUND_GREEN | FOREGROUND_BLUE | FOREGROUND_INTENSITY);
    printf("  DQN TRENING - SNAKE              watki: %d\n", liczbaWatkow);
    SetConsoleTextAttribute(hKonsola, FOREGROUND_GREEN | FOREGROUND_INTENSITY);
    printf("==============================================================\n\n");

    SetConsoleTextAttribute(hKonsola, FOREGROUND_RED | FOREGROUND_GREEN | FOREGROUND_BLUE | FOREGROUND_INTENSITY);
    printf("  EPIZOD:  %d / %d          \n", trenEpizod, trenCalkowity);

    // pasek postępu
    float procent = 100.0f * trenEpizod / (float)trenCalkowity;
    int szerokosc = 50;
    int wypelnione = (int)(szerokosc * (trenEpizod / (float)trenCalkowity));
    printf("  [");
    for (int i = 0; i < szerokosc; i++) {
        SetConsoleTextAttribute(hKonsola, i < wypelnione
            ? (BACKGROUND_GREEN | BACKGROUND_INTENSITY)
            : (BACKGROUND_RED | BACKGROUND_GREEN | BACKGROUND_BLUE));
        putchar(' ');
    }
    SetConsoleTextAttribute(hKonsola, FOREGROUND_RED | FOREGROUND_GREEN | FOREGROUND_BLUE | FOREGROUND_INTENSITY);
    printf("] %5.1f%%   \n", procent);

    // statystyki
    SetConsoleTextAttribute(hKonsola, FOREGROUND_GREEN | FOREGROUND_INTENSITY);
    sprintf(buf, "  BEST: %d    AVG: %lld    EPS: %.3f          \n",
            trenBest > rekord ? trenBest : rekord,
            trenSuma / (trenEpizod ? trenEpizod : 1),
            eps);
    printf("%s", buf);

    sprintf(buf, "  KROKI: %d    REPLAY: %d/%d          \n", krokiGlobalne, replayFill, REPLAY);
    printf("%s", buf);

    double eta = 0.0;
    if (trenEpizod > 0 && sekundy > 0.1) {
        double srCzas = sekundy / trenEpizod;
        eta = srCzas * (trenCalkowity - trenEpizod);
    }
    SetConsoleTextAttribute(hKonsola, FOREGROUND_RED | FOREGROUND_GREEN | FOREGROUND_INTENSITY);
    sprintf(buf, "  ETA: %.0fs    %.1f ep/s    czas: %.0fs          \n",
            eta,
            trenEpizod > 0 ? (float)trenEpizod / (float)sekundy : 0.0f,
            sekundy);
    printf("%s", buf);

    SetConsoleTextAttribute(hKonsola, FOREGROUND_GREEN | FOREGROUND_INTENSITY);
    printf("\n==============================================================\n");
    SetConsoleTextAttribute(hKonsola, FOREGROUND_RED | FOREGROUND_GREEN | FOREGROUND_BLUE);
    fflush(stdout);
}

// ===== TRENING =====
static void trenuj(int epizody, HDC hdc) {
    trenEpizod = 0;
    trenBest = 0;
    trenSuma = 0;
    trenCalkowity = epizody;
    tryb = 2;
    koniecGry = 0;
    pauza = 0;

    wczytajModel();
    EnterCriticalSection(&csReplay);
    replayIdx = 0; replayFill = 0;
    LeaveCriticalSection(&csReplay);
    krokiGlobalne = 0;
    ostatniCzasKonsoli = 0.0;
    ostatniEpKonsoli = -1;

    float eps_start = 1.0f;
    float eps_end = 0.02f;
    int maxKrokow = 1500;

    LARGE_INTEGER freq, start, teraz;
    QueryPerformanceFrequency(&freq);
    QueryPerformanceCounter(&start);

    int ostatniRenderEp = 0;
    LARGE_INTEGER ostatniRenderCzas = start;
    const double RENDER_INTERVAL = 0.2;

    for (int ep = 1; ep <= epizody; ep++) {
        inicjalizujWaza();
        generujJedzenie();
        float stan[WEJSCIA];
        pobierzStan(stan);
        int punktyEp = 0;
        int kroki = 0;

        float eps = eps_start + (eps_end - eps_start) * ((float)ep / epizody);
        if (eps < eps_end) eps = eps_end;

        while (kroki < maxKrokow) {
            int a = wybierzAkcje(stan, eps);

            int nowyKier = akcjaNaKierunek(waz.kierunek, a);
            waz.nastepny_kierunek = nowyKier;

            Punkt ng = waz.cialo[0];
            ng.x += kierDoDx(nowyKier);
            ng.y += kierDoDy(nowyKier);

            int ok = 1, zjada = 0;
            if (ng.x < 0 || ng.x >= GRID_W || ng.y < 0 || ng.y >= GRID_H) ok = 0;
            else {
                zjada = (ng.x == jedzenie.x && ng.y == jedzenie.y);
                int doSprawdz = zjada ? waz.dlugosc : waz.dlugosc - 1;
                for (int i = 0; i < doSprawdz; i++)
                    if (waz.cialo[i].x == ng.x && waz.cialo[i].y == ng.y) { ok = 0; break; }
            }

            float nagroda;
            float nowyStan[WEJSCIA];
            int koniec = 0;

            if (!ok) {
                nagroda = -1000.0f;
                memcpy(nowyStan, stan, sizeof(nowyStan));
                koniec = 1;
            } else {
                for (int i = waz.dlugosc; i > 0; i--) waz.cialo[i] = waz.cialo[i - 1];
                waz.cialo[0] = ng;
                waz.kierunek = nowyKier;

                if (zjada) {
                    waz.dlugosc++;
                    punktyEp += 10;
                    generujJedzenie();
                    nagroda = +100.0f;
                } else {
                    nagroda = -1.0f;
                }
                pobierzStan(nowyStan);
            }

            EnterCriticalSection(&csReplay);
            Doswiadczenie *d = &replay[replayIdx];
            memcpy(d->stan, stan, sizeof(stan));
            d->akcja = a;
            d->nagroda = nagroda;
            memcpy(d->nastepnyStan, nowyStan, sizeof(nowyStan));
            d->koniec = koniec;
            replayIdx = (replayIdx + 1) % REPLAY;
            if (replayFill < REPLAY) replayFill++;
            LeaveCriticalSection(&csReplay);

            if (replayFill >= BATCH) trenujBatchRownolegle();

            krokiGlobalne++;

            // odświeżanie ekranu także w trakcie epizodu
            if ((krokiGlobalne & 63) == 0) {
                QueryPerformanceCounter(&teraz);
                double dtR = (double)(teraz.QuadPart - ostatniRenderCzas.QuadPart) / freq.QuadPart;
                if (dtR >= RENDER_INTERVAL) {
                    double sek = (double)(teraz.QuadPart - start.QuadPart) / freq.QuadPart;
                    rysujPostepKonsoli(eps, sek);
                    rysujEkranTreningu(hdc, eps, sek);
                    ostatniRenderCzas = teraz;
                    ostatniRenderEp = ep;

                    MSG m;
                    while (PeekMessage(&m, NULL, 0, 0, PM_REMOVE)) {
                        if (m.message == WM_QUIT) { PostQuitMessage(0); return; }
                        TranslateMessage(&m);
                        DispatchMessage(&m);
                    }
                }
            }

            if (krokiGlobalne % TARGET_SYNC == 0) {
                EnterCriticalSection(&csSiec);
                kopiujSiec(&siecTarget, &siec);
                LeaveCriticalSection(&csSiec);
            }

            memcpy(stan, nowyStan, sizeof(stan));
            kroki++;
            if (koniec) break;
            if (waz.dlugosc >= MAX_DLUGOSC - 3) { punktyEp += 500; break; }
        }

        if (punktyEp > trenBest) trenBest = punktyEp;
        if (punktyEp > rekord) { rekord = punktyEp; zapiszRekord(); }
        trenSuma += punktyEp;
        trenEpizod = ep;

        aktualizujCzast(0.016f);

        QueryPerformanceCounter(&teraz);
        double dtOdRender = (double)(teraz.QuadPart - ostatniRenderCzas.QuadPart) / freq.QuadPart;
        int epOdRender = ep - ostatniRenderEp;

        if (epOdRender >= 50 || dtOdRender >= RENDER_INTERVAL) {
            double sekundy = (double)(teraz.QuadPart - start.QuadPart) / freq.QuadPart;
            rysujPostepKonsoli(eps, sekundy);
            rysujEkranTreningu(hdc, eps, sekundy);
            zapiszModel();

            ostatniRenderEp = ep;
            ostatniRenderCzas = teraz;

            MSG msg;
            while (PeekMessage(&msg, NULL, 0, 0, PM_REMOVE)) {
                if (msg.message == WM_QUIT) { PostQuitMessage(0); return; }
                TranslateMessage(&msg);
                DispatchMessage(&msg);
            }
        }
    }
    zapiszModel();

    // końcowy stan ekranu i konsoli
    {
        QueryPerformanceCounter(&teraz);
        double sekundy = (double)(teraz.QuadPart - start.QuadPart) / freq.QuadPart;
        ostatniCzasKonsoli = -1.0;
        rysujPostepKonsoli(eps_end, sekundy);
        rysujEkranTreningu(hdc, eps_end, sekundy);
    }

    // podsumowanie w konsoli
    if (konsolaGotowa) {
        COORD pos = {0, 12};
        SetConsoleCursorPosition(hKonsola, pos);
        SetConsoleTextAttribute(hKonsola, BACKGROUND_GREEN | BACKGROUND_INTENSITY | FOREGROUND_RED | FOREGROUND_GREEN | FOREGROUND_BLUE);
        printf("  TRENING ZAKONCZONY!  BEST: %d   AVG: %lld   EPIZODOW: %d   \n",
               trenBest, trenSuma / (trenEpizod ? trenEpizod : 1), trenEpizod);
        SetConsoleTextAttribute(hKonsola, FOREGROUND_RED | FOREGROUND_GREEN | FOREGROUND_BLUE);
        fflush(stdout);
    }

    tryb = 1;
    restart();
}

// ===== KROK GRY =====
static void krokGry(void) {
    if (pauza || koniecGry) return;

    if (tryb == 1) {
        float stan[WEJSCIA];
        pobierzStan(stan);
        int a = wybierzAkcje(stan, 0.0f);
        waz.nastepny_kierunek = akcjaNaKierunek(waz.kierunek, a);
    }

    waz.kierunek = waz.nastepny_kierunek;
    Punkt ng = waz.cialo[0];
    ng.x += kierDoDx(waz.kierunek);
    ng.y += kierDoDy(waz.kierunek);

    int ok = 1;
    if (ng.x < 0 || ng.x >= GRID_W || ng.y < 0 || ng.y >= GRID_H) ok = 0;
    else {
        int zjada = (ng.x == jedzenie.x && ng.y == jedzenie.y);
        int doSprawdz = zjada ? waz.dlugosc : waz.dlugosc - 1;
        for (int i = 0; i < doSprawdz; i++)
            if (waz.cialo[i].x == ng.x && waz.cialo[i].y == ng.y) { ok = 0; break; }
    }

    if (!ok) {
        koniecGry = 1;
        int cx = BOARD_X + waz.cialo[0].x * KOM + KOM/2;
        int cy = BOARD_Y + waz.cialo[0].y * KOM + KOM/2;
        dodajCzast((float)cx, (float)cy, 40, K_JEDZ1, 3.0f);
        return;
    }

    int zjada = (ng.x == jedzenie.x && ng.y == jedzenie.y);
    for (int i = waz.dlugosc; i > 0; i--) waz.cialo[i] = waz.cialo[i - 1];
    waz.cialo[0] = ng;
    if (zjada) {
        waz.dlugosc++;
        punkty += 10;
        if (punkty > rekord) { rekord = punkty; zapiszRekord(); }
        if (punkty % 50 == 0 && predkoscMs > 50) predkoscMs -= 5;
        int cx = BOARD_X + jedzenie.x * KOM + KOM/2;
        int cy = BOARD_Y + jedzenie.y * KOM + KOM/2;
        dodajCzast((float)cx, (float)cy, 16, K_JEDZ1, 2.5f);
        generujJedzenie();
    }
}

// ===== HUD GRY =====
static void rysujHUD(void) {
    char buf[64];
    wypelnijProst(0, 0, WIN_W, 40, 0x00081018, 0.9f);
    wypelnijProst(0, 40, WIN_W, 42, 0x00406080, 1.0f);

    sprintf(buf, "SCORE %d", punkty);
    rysujText(10, 15, buf, K_HUD, 2);

    sprintf(buf, "BEST %d", rekord);
    rysujText(250, 15, buf, K_ZLOTO, 2);

    const char *trybTxt = (tryb == 0) ? "PLAYER" : (tryb == 1) ? "AI DEMO" : "TRAINING";
    uint32_t kolT = (tryb == 0) ? K_HUD : (tryb == 1) ? K_AI : 0x00FF8040;
    rysujText(500, 15, trybTxt, kolT, 2);

    if (pauza) rysujText(700, 15, "PAUSED", 0xFFFFFF, 2);

    if (koniecGry) {
        wypelnijProst(0, 0, WIN_W, WIN_H, 0x000000, 0.65f);
        const char *t = "GAME OVER";
        int w = dlugoscText(t, 6);
        rysujText((WIN_W - w)/2, WIN_H/2 - 80, t, K_JEDZ1, 6);
        const char *t2 = "R - RESTART";
        w = dlugoscText(t2, 2);
        rysujText((WIN_W - w)/2, WIN_H/2, t2, K_HUD, 2);
        const char *t3 = "T - TRAIN  I - AI DEMO";
        w = dlugoscText(t3, 2);
        rysujText((WIN_W - w)/2, WIN_H/2 + 40, t3, K_HUD2, 2);
    }

    int panelY = WIN_H - 70;
    wypelnijProst(0, panelY, WIN_W, WIN_H, 0x00081018, 0.9f);
    wypelnijProst(0, panelY, WIN_W, panelY + 2, 0x00406080, 1.0f);
    rysujText(20, panelY + 15, "WASD/ARROWS - MOVE", K_HUD2, 1);
    rysujText(20, panelY + 30, "T TRAIN  I AI DEMO  SPACE PLAYER", K_HUD2, 1);
    rysujText(20, panelY + 45, "P PAUSE  R RESTART  ESC QUIT", K_HUD2, 1);
}

static void render(void) {
    rysujPlanszeDoBufora();
    rysujJedzenieDoBufora();
    rysujWazDoBufora();
    rysujCzastDoBufora();
    rysujHUD();
}

// ===== AUTODETEKCJA WĄTKÓW =====
static int wykryjLiczbeWatkow(void) {
    SYSTEM_INFO si;
    GetSystemInfo(&si);
    int n = (int)si.dwNumberOfProcessors;
    if (n < 1) n = 1;
    if (n > MAX_WATKOW) n = MAX_WATKOW;
    return n;
}

static void inicjujWatki(void) {
    liczbaWatkow = wykryjLiczbeWatkow();

    watki = (HANDLE*)malloc(sizeof(HANDLE) * liczbaWatkow);
    eventyStart = (HANDLE*)malloc(sizeof(HANDLE) * liczbaWatkow);
    eventyDone = (HANDLE*)malloc(sizeof(HANDLE) * liczbaWatkow);
    gradientyWatkow = (Gradienty*)calloc(liczbaWatkow, sizeof(Gradienty));

    InitializeCriticalSection(&csReplay);
    InitializeCriticalSection(&csSiec);

    for (int i = 0; i < liczbaWatkow; i++) {
        eventyStart[i] = CreateEvent(NULL, FALSE, FALSE, NULL);
        eventyDone[i] = CreateEvent(NULL, FALSE, FALSE, NULL);
    }
    for (int i = 0; i < liczbaWatkow; i++) {
        watki[i] = CreateThread(NULL, 0, watekRoboczy, (LPVOID)(intptr_t)i, 0, NULL);
        SetThreadPriority(watki[i], THREAD_PRIORITY_ABOVE_NORMAL);
    }
}

static void zamknijWatki(void) {
    InterlockedExchange(&watekStop, 1);
    for (int i = 0; i < liczbaWatkow; i++) SetEvent(eventyStart[i]);
    WaitForMultipleObjects(liczbaWatkow, watki, TRUE, 2000);
    for (int i = 0; i < liczbaWatkow; i++) {
        CloseHandle(watki[i]);
        CloseHandle(eventyStart[i]);
        CloseHandle(eventyDone[i]);
    }
    DeleteCriticalSection(&csReplay);
    DeleteCriticalSection(&csSiec);
    free(watki);
    free(eventyStart);
    free(eventyDone);
    free(gradientyWatkow);
}

// ===== WEJSCIE =====
LRESULT CALLBACK WndProc(HWND hwnd, UINT msg, WPARAM wp, LPARAM lp) {
    switch (msg) {
        case WM_DESTROY: PostQuitMessage(0); return 0;
        case WM_ERASEBKGND:
            return 1;   // nie zamalowuj tła na czarno
        case WM_PAINT: {
            PAINTSTRUCT ps;
            HDC h = BeginPaint(hwnd, &ps);
            if (PIXELE)
                StretchDIBits(h, 0, 0, WIN_W, WIN_H, 0, 0, WIN_W, WIN_H,
                              PIXELE, &bmi, DIB_RGB_COLORS, SRCCOPY);
            EndPaint(hwnd, &ps);
            return 0;
        }
        case WM_MOUSEMOVE:
            myszX = LOWORD(lp); myszY = HIWORD(lp);
            return 0;
        case WM_KEYDOWN:
            if (wp == VK_ESCAPE) PostQuitMessage(0);
            else if (wp == 'R') restart();
            else if (wp == 'P') pauza = !pauza;
            else if (wp == 'I') {
                tryb = 1;
                EnterCriticalSection(&csSiec);
                wczytajModel();
                LeaveCriticalSection(&csSiec);
                restart();
            }
            else if (wp == VK_SPACE) {
                tryb = 0;
                restart();
            }
            else if (tryb == 0 && !koniecGry) {
                if (wp == VK_UP    && waz.kierunek != 2) waz.nastepny_kierunek = 0;
                if (wp == VK_RIGHT && waz.kierunek != 3) waz.nastepny_kierunek = 1;
                if (wp == VK_DOWN  && waz.kierunek != 0) waz.nastepny_kierunek = 2;
                if (wp == VK_LEFT  && waz.kierunek != 1) waz.nastepny_kierunek = 3;
                if (wp == 'W' && waz.kierunek != 2) waz.nastepny_kierunek = 0;
                if (wp == 'D' && waz.kierunek != 3) waz.nastepny_kierunek = 1;
                if (wp == 'S' && waz.kierunek != 0) waz.nastepny_kierunek = 2;
                if (wp == 'A' && waz.kierunek != 1) waz.nastepny_kierunek = 3;
            }
            return 0;
    }
    return DefWindowProc(hwnd, msg, wp, lp);
}

// ===== MAIN =====
int WINAPI WinMain(HINSTANCE hInst, HINSTANCE hPrev, LPSTR lpCmd, int nShow) {
    (void)hPrev; (void)lpCmd;
    srand((unsigned)time(NULL));

    SYSTEM_INFO si;
    GetSystemInfo(&si);
    int rdzenie = (int)si.dwNumberOfProcessors;

    PIXELE = (uint32_t*)calloc((size_t)WIN_W * WIN_H, 4);
    ZeroMemory(&bmi, sizeof(bmi));
    bmi.bmiHeader.biSize = sizeof(BITMAPINFOHEADER);
    bmi.bmiHeader.biWidth = WIN_W;
    bmi.bmiHeader.biHeight = -WIN_H;
    bmi.bmiHeader.biPlanes = 1;
    bmi.bmiHeader.biBitCount = 32;
    bmi.bmiHeader.biCompression = BI_RGB;

    WNDCLASS wc = {0};
    wc.lpfnWndProc = WndProc;
    wc.hInstance = hInst;
    wc.hCursor = LoadCursor(NULL, IDC_ARROW);
    wc.hbrBackground = (HBRUSH)GetStockObject(BLACK_BRUSH);
    wc.lpszClassName = "SnakeDQNMT";
    RegisterClass(&wc);

    char tytul[128];
    sprintf(tytul, "Snake DQN - %d rdzeni / %d watkow",
            rdzenie, wykryjLiczbeWatkow());

    RECT r = {0, 0, WIN_W, WIN_H};
    AdjustWindowRect(&r, WS_OVERLAPPEDWINDOW, FALSE);
    HWND hwnd = CreateWindow("SnakeDQNMT", tytul,
                             WS_OVERLAPPEDWINDOW,
                             CW_USEDEFAULT, CW_USEDEFAULT,
                             r.right - r.left, r.bottom - r.top,
                             NULL, NULL, hInst, NULL);
    ShowWindow(hwnd, nShow);

    HDC hdc = GetDC(hwnd);

    inicjujWatki();
    inicjujKonsole();
    wczytajRekord();
    wczytajModel();
    restart();

    LARGE_INTEGER freq, last, now;
    QueryPerformanceFrequency(&freq);
    QueryPerformanceCounter(&last);

    int running = 1;
    int treningZadany = 0;

    while (running) {
        MSG msg;
        while (PeekMessage(&msg, NULL, 0, 0, PM_REMOVE)) {
            if (msg.message == WM_QUIT) running = 0;
            TranslateMessage(&msg);
            DispatchMessage(&msg);
            if (msg.message == WM_KEYDOWN && msg.wParam == 'T') treningZadany = 1;
        }
        if (!running) break;

        if (treningZadany) {
            treningZadany = 0;
            trenuj(EPIZODY_TRENINGU, hdc);
            QueryPerformanceCounter(&last);
            continue;
        }

        QueryPerformanceCounter(&now);
        float dt = (float)(now.QuadPart - last.QuadPart) / (float)freq.QuadPart;
        last = now;
        if (dt > 0.1f) dt = 0.1f;
        czasAnim += dt;

        if (tryb != 2) {
            akumulatorRuchu += dt * 1000.0f;
            if (akumulatorRuchu >= predkoscMs) {
                akumulatorRuchu = 0;
                krokGry();
            }
        }
        aktualizujCzast(dt);

        render();
        StretchDIBits(hdc, 0, 0, WIN_W, WIN_H,
                      0, 0, WIN_W, WIN_H,
                      PIXELE, &bmi, DIB_RGB_COLORS, SRCCOPY);
    }

    zamknijWatki();
    ReleaseDC(hwnd, hdc);
    free(PIXELE);
    return 0;
}

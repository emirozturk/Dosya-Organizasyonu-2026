// =====================================================================
//  Dosya Organizasyonu · Hafta 1–7 · Yöntemlerin karşılaştırılması
//
//  Derleme : g++ -std=c++17 -O2 -o karsilastirma karsilastirma.cpp
//  Çalıştırma: ./karsilastirma            (n ve doluluk sorulur)
//              ./karsilastirma 10000 0.9  (komut satırından da verilebilir)
//
//  Program iki grup yöntemi aynı veriyle çalıştırır:
//
//  A) Arama yöntemleri (hafta 2–3)
//     sıralı arama, ikili arama, ara değer arama,
//     kendini düzenleyen sıralı arama: öne taşıma, konum değiştirme, sayaç
//
//  B) Hashing ve collision (çarpışma) çözümleme (hafta 4–7)
//     progressive overflow, linear quotient, LISCH, EISCH, LICH,
//     Brent's metodu, binary tree method (ikili ağaç), computed chaining
//
//  Her yöntem için iki ölçü verilir:
//   - probe: aranan kayda ulaşmak için bakılan göz (ya da karşılaştırılan
//     kayıt) sayısı. Dosya üzerinde her probe bir disk erişimine karşılık
//     gelir; derste "maliyet" dediğimiz büyüklük budur.
//   - süre: bellekte ölçülen gerçek süre (milisaniye). Probe sayısı aynı
//     olsa bile işlem başına yapılan hesap farklı olduğundan süre değişir.
//
//  Anahtarlar sabit tohumla üretilir: program her çalıştırmada aynı
//  anahtarları kullanır, sonuçlar yinelenebilir.
// =====================================================================

#include <algorithm>
#include <chrono>
#include <cmath>
#include <functional>
#include <iomanip>
#include <iostream>
#include <numeric>
#include <random>
#include <sstream>
#include <string>
#include <unordered_set>
#include <vector>
using namespace std;

constexpr int BOS = -1;                 // boş göz işareti

// ---------------------------------------------------------------------
//  Yardımcılar: süre ölçümü ve asal sayı
// ---------------------------------------------------------------------
using Saat = chrono::steady_clock;

double ms_gecen(Saat::time_point bas) {
    return chrono::duration<double, milli>(Saat::now() - bas).count();
}

bool asal_mi(int x) {
    if (x < 2) return false;
    for (int d = 2; 1LL * d * d <= x; ++d)
        if (x % d == 0) return false;
    return true;
}

// Tablo boyu asal seçilir: linear quotient ve türevlerinde artım ile
// tablo boyunun aralarında asal olması gerekir (hafta 4). Asal boyda
// 1..m-1 arasındaki her artım bütün gözleri dolaşır.
int asal_ust(int x) {
    while (!asal_mi(x)) ++x;
    return x;
}

// Sonuç satırı: her yöntem için tabloya yazılacak değerler
struct Sonuc {
    string ad;
    double ekleme_ms = 0;               // bütün anahtarların eklenme süresi
    double arama_ms = 0;                // bütün aramaların süresi
    double basarili = 0;                // başarılı aramada ortalama probe
    double basarisiz = -1;              // başarısız aramada ortalama probe
    int en_cok = 0;                     // başarılı aramada en kötü durum
    int eklenemeyen = 0;                // yer bulunamayan anahtar sayısı
    int bulunamayan = 0;                // eklendiği halde bulunamayan (hata denetimi)
};

// =====================================================================
//  A) ARAMA YÖNTEMLERİ
// =====================================================================

// Sıralı arama: baştan başlayıp her kayda bakar. Probe = bakılan kayıt.
int sirali(const vector<int>& a, int k) {
    for (size_t i = 0; i < a.size(); ++i)
        if (a[i] == k) return int(i) + 1;
    return int(a.size());               // bulunamadı: hepsine bakıldı
}

// İkili arama: sıralı dizide ortadaki kayda bakarak aralığı yarılar.
int ikili(const vector<int>& a, int k) {
    int alt = 0, ust = int(a.size()) - 1, p = 0;
    while (alt <= ust) {
        int orta = alt + (ust - alt) / 2;
        ++p;
        if (a[orta] == k) return p;
        if (a[orta] < k) alt = orta + 1;
        else ust = orta - 1;
    }
    return p;
}

// Ara değer arama: anahtarın değerine göre konumu tahmin eder.
// Düzgün dağılımda çok az adımda bulur; çarpık dağılımda kötüleşir.
int ara_deger(const vector<int>& a, int k) {
    int alt = 0, ust = int(a.size()) - 1, p = 0;
    while (alt <= ust && k >= a[alt] && k <= a[ust]) {
        ++p;
        if (a[ust] == a[alt]) return p;
        long long pay = 1LL * (k - a[alt]) * (ust - alt);
        int orta = alt + int(pay / (a[ust] - a[alt]));
        if (a[orta] == k) return p;
        if (a[orta] < k) alt = orta + 1;
        else ust = orta - 1;
    }
    return max(p, 1);
}

// Kendini düzenleyen sıralı arama (hafta 3). Liste sırasız tutulur;
// her bulunan kayıt öne doğru yaklaştırılır. Sık aranan kayıtlar başa
// toplandıkça probe sayısı düşer. Bu yüzden bu yöntemler, bazı kayıtların
// çok daha sık arandığı çarpık bir erişim dizisiyle denenir.
int one_tasi(vector<int>& v, int k) {
    for (size_t i = 0; i < v.size(); ++i)
        if (v[i] == k) {
            rotate(v.begin(), v.begin() + i, v.begin() + i + 1);
            return int(i) + 1;
        }
    return int(v.size());
}

int konum_degistir(vector<int>& v, int k) {
    for (size_t i = 0; i < v.size(); ++i)
        if (v[i] == k) {
            if (i > 0) swap(v[i - 1], v[i]);
            return int(i) + 1;
        }
    return int(v.size());
}

int sayac_ara(vector<pair<int, int>>& v, int k) {
    for (size_t i = 0; i < v.size(); ++i)
        if (v[i].first == k) {
            ++v[i].second;
            for (size_t j = i; j > 0 && v[j - 1].second < v[j].second; --j)
                swap(v[j - 1], v[j]);
            return int(i) + 1;
        }
    return int(v.size());
}

// Bir arama yöntemini verilen arama dizisiyle çalıştırıp ölçer
Sonuc olc_arama(const string& ad, const vector<int>& aramalar,
                const function<int(int)>& ara) {
    Sonuc s;
    s.ad = ad;
    long long toplam = 0;
    auto bas = Saat::now();
    for (int k : aramalar) {
        int p = ara(k);
        toplam += p;
        s.en_cok = max(s.en_cok, p);
    }
    s.arama_ms = ms_gecen(bas);
    s.basarili = double(toplam) / aramalar.size();
    return s;
}

// =====================================================================
//  B) HASHING VE ÇARPIŞMA ÇÖZÜMLEME
// =====================================================================
//
//  Bütün yöntemler aynı iki fonksiyonu kullanır (derste olduğu gibi):
//    ev adresi     H(k) = k mod m
//    artım (adım)  f(k) = bölüm(k / m) mod m, sıfırsa 1
//  Artım her anahtar için farklıdır: aynı ev adresine düşen anahtarlar
//  farklı adımlarla ilerlediği için kümelenme azalır (hafta 4).

struct Hash {
    int m;
    int ev(int k) const { return k % m; }
    int artim(int k) const { int a = (k / m) % m; return a == 0 ? 1 : a; }
};

// Her yöntemin uyması gereken arayüz: ekle ve ara (probe döndürür)
struct Yontem {
    virtual ~Yontem() = default;
    virtual bool ekle(int k) = 0;       // false: yer bulunamadı
    virtual int ara(int k) const = 0;   // bulunduysa +probe, yoksa -probe
};

// ---------------------------------------------------------------------
//  1. Progressive overflow (hafta 4): dolu gözde bir sonrakine geçilir.
//  Hiç bağlantı yok; bedeli birincil kümelenme (clustering).
// ---------------------------------------------------------------------
struct Progressive : Yontem {
    Hash h; vector<int> t;
    explicit Progressive(int m) : h{m}, t(m, BOS) {}
    bool ekle(int k) override {
        for (int i = 0, a = h.ev(k); i < h.m; ++i, a = (a + 1) % h.m)
            if (t[a] == BOS) { t[a] = k; return true; }
        return false;
    }
    int ara(int k) const override {
        int a = h.ev(k);
        for (int p = 1; p <= h.m; ++p, a = (a + 1) % h.m)
            if (t[a] == k) return p;                   // bulundu
            else if (t[a] == BOS) return -p;          // boşa varıldı: yok
        return -h.m;
    }
};

// ---------------------------------------------------------------------
//  2. Linear quotient (hafta 4): adım 1 yerine anahtara özgü f(k).
// ---------------------------------------------------------------------
struct LinearQuotient : Yontem {
    Hash h; vector<int> t;
    explicit LinearQuotient(int m) : h{m}, t(m, BOS) {}
    bool ekle(int k) override {
        int a = h.ev(k), d = h.artim(k);
        for (int i = 0; i < h.m; ++i, a = (a + d) % h.m)
            if (t[a] == BOS) { t[a] = k; return true; }
        return false;
    }
    int ara(int k) const override {
        int a = h.ev(k), d = h.artim(k);
        for (int p = 1; p <= h.m; ++p, a = (a + d) % h.m)
            if (t[a] == k) return p;
            else if (t[a] == BOS) return -p;
        return -h.m;
    }
};

// ---------------------------------------------------------------------
//  3–5. Coalesced hashing (hafta 5): her gözde bir bağlantı alanı.
//  Çarpışan kayıt tablonun en altındaki boş göze yazılır ve zincire
//  bağlanır. Arama yalnızca kendi zincirini izler.
//    LISCH: yeni kayıt zincirin sonuna bağlanır
//    EISCH: yeni kayıt ev adresinin hemen arkasına bağlanır
//    LICH : tablonun alt kısmı (yaklaşık %14) ev adresi olarak kullanılmaz,
//           taşma alanı (cellar) olarak ayrılır; zincirler daha geç birleşir
//  Boş göz işaretçisi (R) yalnızca aşağıdan yukarı tek yönde ilerler;
//  böylece boş göz aramak her eklemede baştan tarama gerektirmez.
// ---------------------------------------------------------------------
struct Coalesced : Yontem {
    int m, adres_alani; bool erken;
    vector<int> t, bag;
    int R;                               // sıradaki boş göz adayı
    Coalesced(int m_, bool erken_, double cellar_orani)
        : m(m_), erken(erken_), t(m_, BOS), bag(m_, -1), R(m_ - 1) {
        adres_alani = max(1, int(lround(m * (1.0 - cellar_orani))));
    }
    int ev(int k) const { return k % adres_alani; }
    bool ekle(int k) override {
        int e = ev(k);
        if (t[e] == BOS) { t[e] = k; return true; }
        while (R >= 0 && t[R] != BOS) --R;              // en alttaki boş göz
        if (R < 0) return false;
        t[R] = k;
        if (erken) { bag[R] = bag[e]; bag[e] = R; }     // ev adresinin arkasına
        else {                                          // zincirin sonuna
            int son = e;
            while (bag[son] != -1) son = bag[son];
            bag[son] = R;
        }
        return true;
    }
    int ara(int k) const override {
        int a = ev(k), p = 1;
        if (t[a] == BOS) return -1;
        while (t[a] != k && bag[a] != -1) { a = bag[a]; ++p; }
        return t[a] == k ? p : -p;
    }
};

// ---------------------------------------------------------------------
//  6. Brent's metodu (hafta 5): linear quotient üzerine kurulur.
//  Yeni kaydın kendi yolu uzunsa, yolundaki bir kaydı kendi artımıyla
//  ilerletip yerini almayı dener: i + j toplamı en küçük olan seçilir.
//  Arama değişmez: herkes kendi linear quotient yolunda aranır.
// ---------------------------------------------------------------------
bool brent_ekle(const Hash& h, vector<int>& t, int k) {
    const int m = h.m, e = h.ev(k), d = h.artim(k);
    if (t[e] == BOS) { t[e] = k; return true; }
    int s = 2, yer = (e + d) % m;                   // yeni kaydın kendi yolu
    while (t[yer] != BOS) {
        yer = (yer + d) % m;
        if (++s > m) return false;
    }
    for (int top = 2; top < s; ++top)               // daha ucuz bir taşıma var mı
        for (int i = 1; i < top; ++i) {
            int j = top - i;
            int p = int((e + 1LL * (i - 1) * d) % m);   // yoldaki i. kayıt
            int hedef = int((p + 1LL * j * h.artim(t[p])) % m);
            if (t[hedef] == BOS) {                  // o kaydı j adım ilerlet
                t[hedef] = t[p];
                t[p] = k;
                return true;
            }
        }
    t[yer] = k;
    return true;
}

struct Brent : Yontem {
    Hash h; vector<int> t;
    explicit Brent(int m) : h{m}, t(m, BOS) {}
    bool ekle(int k) override { return brent_ekle(h, t, k); }
    int ara(int k) const override {
        int a = h.ev(k), d = h.artim(k);
        for (int p = 1; p <= h.m; ++p, a = (a + d) % h.m)
            if (t[a] == k) return p;
            else if (t[a] == BOS) return -p;
        return -h.m;
    }
};

// ---------------------------------------------------------------------
//  7. Binary tree method (hafta 6): Brent'in tek taşımasını genelleştirir.
//  Her düğümde iki seçenek: yeni kayıt devam eder (continue) ya da
//  yerleşik kayıt taşınır (move). Ağaç genişlik öncelikli kurulur; ilk
//  bulunan boş göz en az toplam adımı verir. Arama linear quotient'tir.
// ---------------------------------------------------------------------
struct IkiliAgac : Yontem {
    struct Dugum { int adres, anahtar, ebeveyn; bool tasima; };
    Hash h; vector<int> t;
    explicit IkiliAgac(int m) : h{m}, t(m, BOS) {}
    bool ekle(int k) override {
        const int m = h.m;
        vector<Dugum> d{{h.ev(k), k, -1, false}};
        const size_t sinir = min<size_t>(4u * m, 1u << 14);      // en çok düğüm
        for (size_t i = 0; i < d.size() && d.size() < sinir; ++i) {
            Dugum x = d[i];
            if (t[x.adres] == BOS) {
                t[x.adres] = x.anahtar;
                for (int j = int(i); d[j].ebeveyn != -1; j = d[j].ebeveyn)
                    if (d[j].tasima) {                  // taşınan kaydın yerine ebeveyn
                        const Dugum& e = d[d[j].ebeveyn];
                        t[e.adres] = e.anahtar;
                    }
                return true;
            }
            d.push_back({(x.adres + h.artim(x.anahtar)) % m, x.anahtar, int(i), false});
            d.push_back({(x.adres + h.artim(t[x.adres])) % m, t[x.adres], int(i), true});
        }
        // Ağaç sınırı aşıldı (tablo çok dolu, ağaç üstel büyüyor): yer
        // Brent'in tek taşımalı yöntemiyle bulunur.
        return brent_ekle(h, t, k);
    }
    int ara(int k) const override {
        int a = h.ev(k), dd = h.artim(k);
        for (int p = 1; p <= h.m; ++p, a = (a + dd) % h.m)
            if (t[a] == k) return p;
            else if (t[a] == BOS) return -p;
        return -h.m;
    }
};

// ---------------------------------------------------------------------
//  8. Computed chaining (hafta 7): bağlantı alanında adres değil küçük
//  bir çarpan tutulur. Sonraki adres = adres + çarpan × f(o adresteki kayıt).
//  Ev adresi başka zincirin kaydıyla doluysa o kayıt ve ardındakiler
//  zincir boyunca ilerletilir; böylece her zincir kendi ev adresinden başlar.
// ---------------------------------------------------------------------
struct Computed : Yontem {
    Hash h; vector<int> t, carpan;
    explicit Computed(int m) : h{m}, t(m, BOS), carpan(m, 0) {}
    int sonraki(int a) const {
        return int((a + 1LL * carpan[a] * h.artim(t[a])) % h.m);
    }
    bool sona_ekle(int k) {
        int son = h.ev(k);
        while (carpan[son] != 0) son = sonraki(son);    // zincirin son kaydı
        int d = h.artim(t[son]);                        // son kaydın artımı
        for (int j = 1; j < h.m; ++j) {
            int a = int((son + 1LL * j * d) % h.m);
            if (t[a] == BOS) { carpan[son] = j; t[a] = k; return true; }
        }
        return false;
    }
    bool ekle(int k) override {
        const int e = h.ev(k);
        if (t[e] == BOS) { t[e] = k; carpan[e] = 0; return true; }
        const int sahip = h.ev(t[e]);
        if (sahip == e) return sona_ekle(k);            // yerleşik kayıt kendi evinde
        int once = sahip;                               // e'yi gösteren kayıt
        while (sonraki(once) != e) once = sonraki(once);
        vector<int> tasinan;                            // e ve ardındakiler
        for (int a = e;;) {
            tasinan.push_back(t[a]);
            int s = carpan[a] ? sonraki(a) : -1;
            t[a] = BOS; carpan[a] = 0;
            if (s < 0) break;
            a = s;
        }
        carpan[once] = 0;
        t[e] = k;
        bool tamam = true;
        for (int x : tasinan) tamam = sona_ekle(x) && tamam;
        return tamam;
    }
    int ara(int k) const override {
        int a = h.ev(k), p = 1;
        if (t[a] == BOS || h.ev(t[a]) != a) return -1;  // ev adresinde zincir yok
        while (t[a] != k && carpan[a] != 0) { a = sonraki(a); ++p; }
        return t[a] == k ? p : -p;
    }
};

// Bir hashing yöntemini çalıştırıp ölçer
Sonuc olc_hash(const string& ad, Yontem& y, const vector<int>& anahtarlar,
               const vector<int>& olmayanlar) {
    Sonuc s;
    s.ad = ad;
    auto bas = Saat::now();
    for (int k : anahtarlar)
        if (!y.ekle(k)) ++s.eklenemeyen;
    s.ekleme_ms = ms_gecen(bas);

    long long top1 = 0, top2 = 0;
    bas = Saat::now();
    for (int k : anahtarlar) {                 // başarılı aramalar
        int p = y.ara(k);
        if (p < 0) { ++s.bulunamayan; p = -p; }  // eklenmiş anahtar bulunamadıysa hata
        top1 += p;
        s.en_cok = max(s.en_cok, p);
    }
    for (int k : olmayanlar) top2 += abs(y.ara(k)); // başarısız aramalar
    s.arama_ms = ms_gecen(bas);
    s.basarili = double(top1) / anahtarlar.size();
    s.basarisiz = double(top2) / olmayanlar.size();
    return s;
}

// =====================================================================
//  Çıktı
// =====================================================================
void tablo_yaz(const string& baslik, vector<Sonuc> v, bool hash) {
    cout << "\n" << baslik << "\n" << string(baslik.size(), '-') << "\n";
    cout << left << setw(26) << "yontem" << right;
    if (hash) cout << setw(11) << "ekleme ms";
    cout << setw(10) << "arama ms" << setw(11) << "basarili"
         << (hash ? "  basarisiz" : "") << setw(9) << "en cok";
    if (hash) cout << setw(12) << "eklenemedi";
    cout << "\n";
    for (const auto& s : v) {
        cout << left << setw(26) << s.ad << right << fixed;
        if (hash) cout << setw(11) << setprecision(3) << s.ekleme_ms;
        cout << setw(10) << setprecision(3) << s.arama_ms
             << setw(11) << setprecision(2) << s.basarili;
        if (hash) cout << setw(11) << setprecision(2) << s.basarisiz;
        cout << setw(9) << s.en_cok;
        if (hash) cout << setw(12) << s.eklenemeyen;
        if (s.bulunamayan) cout << "  UYARI: " << s.bulunamayan << " anahtar bulunamadi";
        cout << "\n";
    }
    // en iyi yöntem: önce ortalama probe, sonra süre
    auto az = min_element(v.begin(), v.end(), [](const Sonuc& a, const Sonuc& b) {
        return a.basarili < b.basarili; });
    auto hizli = min_element(v.begin(), v.end(), [](const Sonuc& a, const Sonuc& b) {
        return a.arama_ms < b.arama_ms; });
    cout << "-> en az probe : " << az->ad << " (" << setprecision(2) << az->basarili << ")\n";
    cout << "-> en hizli    : " << hizli->ad << " (" << setprecision(3) << hizli->arama_ms << " ms)\n";
}

int main(int argc, char* argv[]) {
    int n = 0;
    double doluluk = 0.9;
    if (argc >= 2) {
        n = atoi(argv[1]);
        if (argc >= 3) doluluk = atof(argv[2]);
    } else {
        cout << "Anahtar sayisi n: ";
        cin >> n;
        cout << "Doluluk orani (0.1-0.99, Enter = 0.9): ";
        string satir;
        getline(cin, satir);            // n'den kalan satır sonu
        getline(cin, satir);
        if (!satir.empty()) doluluk = stod(satir);
    }
    if (n < 10 || doluluk <= 0 || doluluk >= 1) {
        cerr << "n en az 10, doluluk 0 ile 1 arasinda olmali\n";
        return 1;
    }

    // ---- veri: n farklı anahtar, düzgün dağılımlı, sabit tohum
    mt19937 rng(2026);
    uniform_int_distribution<int> dag(0, max(10 * n, 1000));
    unordered_set<int> kume;
    vector<int> anahtarlar;
    while (int(anahtarlar.size()) < n) {
        int k = dag(rng);
        if (kume.insert(k).second) anahtarlar.push_back(k);
    }
    vector<int> olmayanlar;             // tabloda bulunmayan n anahtar
    while (int(olmayanlar.size()) < n) {
        int k = dag(rng);
        if (!kume.count(k)) olmayanlar.push_back(k);
    }

    cout << "\nn = " << n << " anahtar, doluluk = " << doluluk << "\n";

    // ---- A) Arama yöntemleri
    // O(n) yöntemler n arama için n² iş yapar; büyük n'de beklememek için
    // arama sayısı en çok 2000 ile sınırlanır (ortalama değişmez).
    const int q = min(n, 2000);
    vector<int> sirali_dizi = anahtarlar;
    sort(sirali_dizi.begin(), sirali_dizi.end());
    vector<int> rastgele_aramalar(anahtarlar.begin(), anahtarlar.begin() + q);

    // Kendini düzenleyen yöntemler için çarpık erişim: Zipf dağılımı.
    // r. sıradaki kaydın aranma olasılığı 1/r ile orantılı.
    vector<double> agirlik(n);
    for (int r = 0; r < n; ++r) agirlik[r] = 1.0 / (r + 1);
    discrete_distribution<int> zipf(agirlik.begin(), agirlik.end());
    // Sık aranan kayıtlar listenin başında değil, rastgele yerlerindedir:
    // sıra numarası (r) anahtarlara karıştırılarak atanır.
    vector<int> sira = anahtarlar;
    shuffle(sira.begin(), sira.end(), rng);
    vector<int> carpik_aramalar(q);
    for (int& x : carpik_aramalar) x = sira[zipf(rng)];

    vector<Sonuc> a;
    a.push_back(olc_arama("sirali (rastgele erisim)", rastgele_aramalar,
                          [&](int k) { return sirali(anahtarlar, k); }));
    a.push_back(olc_arama("ikili", rastgele_aramalar,
                          [&](int k) { return ikili(sirali_dizi, k); }));
    a.push_back(olc_arama("ara deger", rastgele_aramalar,
                          [&](int k) { return ara_deger(sirali_dizi, k); }));
    tablo_yaz("A1) Siralanmis dizide arama  (" + to_string(q) + " arama)", a, false);

    vector<int> l1 = anahtarlar, l2 = anahtarlar;
    vector<pair<int, int>> l3;
    for (int k : anahtarlar) l3.push_back({k, 0});
    vector<Sonuc> b;
    b.push_back(olc_arama("sirali (carpik erisim)", carpik_aramalar,
                          [&](int k) { return sirali(anahtarlar, k); }));
    b.push_back(olc_arama("one tasima", carpik_aramalar,
                          [&](int k) { return one_tasi(l1, k); }));
    b.push_back(olc_arama("konum degistirme", carpik_aramalar,
                          [&](int k) { return konum_degistir(l2, k); }));
    b.push_back(olc_arama("sayac", carpik_aramalar,
                          [&](int k) { return sayac_ara(l3, k); }));
    tablo_yaz("A2) Kendini duzenleyen sirali arama  (Zipf erisimi, " +
              to_string(q) + " arama)", b, false);

    // ---- B) Hashing: aynı anahtarlar, aynı tablo boyu
    const int m = asal_ust(int(ceil(n / doluluk)));
    cout << "\nTablo boyu m = " << m << " (n / doluluk degerinden buyuk ilk asal)\n";

    vector<Sonuc> c;
    { Progressive y(m);          c.push_back(olc_hash("progressive overflow", y, anahtarlar, olmayanlar)); }
    { LinearQuotient y(m);       c.push_back(olc_hash("linear quotient", y, anahtarlar, olmayanlar)); }
    { Coalesced y(m, false, 0);  c.push_back(olc_hash("LISCH", y, anahtarlar, olmayanlar)); }
    { Coalesced y(m, true, 0);   c.push_back(olc_hash("EISCH", y, anahtarlar, olmayanlar)); }
    { Coalesced y(m, false, 0.14); c.push_back(olc_hash("LICH (cellar %14)", y, anahtarlar, olmayanlar)); }
    { Brent y(m);                c.push_back(olc_hash("Brent", y, anahtarlar, olmayanlar)); }
    { IkiliAgac y(m);            c.push_back(olc_hash("ikili agac", y, anahtarlar, olmayanlar)); }
    { Computed y(m);             c.push_back(olc_hash("computed chaining", y, anahtarlar, olmayanlar)); }
    tablo_yaz("B) Hashing ve carpisma cozumleme  (" + to_string(n) +
              " basarili + " + to_string(n) + " basarisiz arama)", c, true);

    cout << "\nNotlar\n"
         << "- basarili / basarisiz: arama basina ortalama probe (dosyada disk erisimi)\n"
         << "- en cok: en kotu basarili aramanin probe sayisi\n"
         << "- sure olcumu makineye baglidir; probe sayisi makineden bagimsizdir\n"
         << "- coalesced yontemlerde her gozde ayrica bir baglanti alani vardir;\n"
         << "  computed chaining yalnizca kucuk bir carpan, digerleri hic alan tutmaz\n"
         << "- bu programda computed chaining carpanina bit siniri konmamistir;\n"
         << "  gercek uygulamada carpan birkac bitle sinirlidir\n";
}

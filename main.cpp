/**
 * ============================================================================
 * CHUONG TRINH QUAN LY TAI KHOAN NGAN HANG (C++ OOP)
 * Mon hoc: Lap trinh huong doi tuong (Object-Oriented Programming)
 * 
 * CAC NGUYEN TAC THIET KE OOP & TINH NANG:
 * 1. Dong goi (Encapsulation):
 *    - Toan bo thong tin nhay cam (mat khau, ma PIN, salt) va so du duoc dong goi
 *      chat che (private/protected). Khong cho phep truy cap hay sua doi tuy tien
 *      tu ben ngoai. Loai bo setSoDuCongKhai de dam bao an toan tuyet doi.
 *    - So du chi duoc cap nhat thong qua quy trinh xac thuc PIN nghiem ngat.
 * 2. Ke thua (Inheritance):
 *    - Lop co so truu tuong TaiKhoan.
 *    - Lop dan xuat TaiKhoanTietKiem (bo sung lai suat %/nam).
 *    - Lop dan xuat TaiKhoanThanhToan (bo sung han muc tin dung).
 * 3. Da hinh & Template Method Pattern (Polymorphism):
 *    - Phuong thuc ao: CoTheRut(), getSoDuKhaDung(), RutTien(), HienThiThongTin(),
 *      getLoaiTaiKhoan(), NhapThuocTinhRieng(), XuatThuocTinhRieng().
 *    - Quy tac rut tien khac biet: TaiKhoanTietKiem khong duoc am so du,
 *      TaiKhoanThanhToan cho phep so du am toi da trong han muc tin dung.
 *    - RutTien va NapTien o muc protected; cac phuong thuc cong khai bat buoc
 *      xac thuc PIN truoc khi uy quyen cho phuong thuc da hinh cot loi.
 * 4. Nap chong toan tu (Operator Overloading):
 *    - operator>> va operator<< cho TaiKhoan va GiaoDich.
 * 5. Quan ly bo nho an toan:
 *    - Su dung std::unique_ptr<TaiKhoan> va std::vector de tranh ro ri bo nho.
 * 6. Bao mat & Xac thuc:
 *    - Băm mat khau va PIN bang thuat toan SHA-256 kem Per-Account Salt.
 *    - Ma PIN 6 chu so co dinh, giu nguyen chu so 0 o dau.
 *    - Mat khau va PIN doc lap, khong cho phep dat giong nhau.
 *    - Khoa tai khoan khi nhap sai mat khau 5 lan hoac sai PIN 3 lan.
 *    - Quy trinh dang nhap, dang xuat, doi mat khau va doi PIN an toan.
 * 7. Quan ly giao dich & Tinh nhat quan:
 *    - Lop GiaoDich luu ma duy nhat, loai, thoi gian, so du truoc/sau, phi.
 *    - Chuyen tien nguyen tu (atomic): chi tru nguon khi cong dich thanh cong.
 * 8. Phan quyen Admin / Khach hang:
 *    - Khach hang chi thao tac tren tai khoan da dang nhap.
 *    - Admin co quyen mo khoa tai khoan, thong ke toan ngan hang, tinh lai tiet kiem.
 * 9. Tinh nang mo rong:
 *    - Canh bao so du xuong duoi nguong.
 *    - Xuat sao ke ra tap tin TXT / CSV.
 *    - Luu va khoi phuc du lieu he thong (File Persistence).
 * ============================================================================
 */

#include <iostream>
#include <iomanip>
#include <string>
#include <vector>
#include <memory>
#include <limits>
#include <stdexcept>
#include <algorithm>
#include <sstream>
#include <fstream>
#include <chrono>
#include <ctime>
#include <cstdint>
#include <random>
#include <cctype>
#include <cmath>

#ifdef _WIN32
#ifndef NOMINMAX
#define NOMINMAX
#endif
#include <windows.h>
#include <conio.h>
#include <io.h>
#ifndef ENABLE_VIRTUAL_TERMINAL_PROCESSING
#define ENABLE_VIRTUAL_TERMINAL_PROCESSING 0x0004
#endif
#else
#include <termios.h>
#include <unistd.h>
#endif

using namespace std;

// ============================================================================
// HANG SO HE THONG VA QUY TAC NGHIEP VU
// ============================================================================
namespace BankConstants {
    const double HAN_MUC_RUT_MOI_LAN_TOI_DA  = 20000000.0; // 20 trieu VND / lan
    const double HAN_MUC_RUT_MOI_LAN_TOI_THIEU = 50000.0;   // 50 nghin VND / lan
    const double HAN_MUC_RUT_NGAY_TOI_DA     = 50000000.0; // 50 trieu VND / ngay
    const double PHI_CHUYEN_TIEN_CO_DINH     = 2000.0;     // 2.000 VND / giao dich
    const double NGUONG_CANH_BAO_MAC_DINH    = 50000.0;    // 50.000 VND
    const int    MAX_SAI_MAT_KHAU            = 5;          // Khoa sau 5 lan sai MK
    const int    MAX_SAI_PIN                 = 3;          // Khoa sau 3 lan sai PIN
    const size_t DO_DAI_PIN_YEU_CAU          = 6;          // PIN gom 6 chu so
    const string FILE_DU_LIEU_MAC_DINH       = "bank_data.txt";
}

// ============================================================================
// MODULE AN TOAN & MA HOA (SECURITY & CRYPTO UTILITIES)
// ============================================================================
namespace Security {

    inline uint32_t rotr(uint32_t x, uint32_t n) {
        return (x >> n) | (x << (32 - n));
    }
    inline uint32_t choose(uint32_t e, uint32_t f, uint32_t g) {
        return (e & f) ^ (~e & g);
    }
    inline uint32_t majority(uint32_t a, uint32_t b, uint32_t c) {
        return (a & b) ^ (a & c) ^ (b & c);
    }
    inline uint32_t sig0(uint32_t x) {
        return rotr(x, 2) ^ rotr(x, 13) ^ rotr(x, 22);
    }
    inline uint32_t sig1(uint32_t x) {
        return rotr(x, 6) ^ rotr(x, 11) ^ rotr(x, 25);
    }
    inline uint32_t theta0(uint32_t x) {
        return rotr(x, 7) ^ rotr(x, 18) ^ (x >> 3);
    }
    inline uint32_t theta1(uint32_t x) {
        return rotr(x, 17) ^ rotr(x, 19) ^ (x >> 10);
    }

    const uint32_t K[64] = {
        0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5, 0x3956c25b, 0x59f111f1, 0x923f82a4, 0xab1c5ed5,
        0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3, 0x72be5d74, 0x80deb1fe, 0x9bdc06a7, 0xc19bf174,
        0xe49b69c1, 0xefbe4786, 0x0fc19dc6, 0x240ca1cc, 0x2de92c6f, 0x4a7484aa, 0x5cb0a9dc, 0x76f988da,
        0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7, 0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967,
        0x27b70a85, 0x2e1b2138, 0x4d2c6dfc, 0x53380d13, 0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85,
        0xa2bfe8a1, 0xa81a664b, 0xc24b8b70, 0xc76c51a3, 0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070,
        0x19a4c116, 0x1e376c08, 0x2748774c, 0x34b0bcb5, 0x391c0cb3, 0x4ed8aa4a, 0x5b9cca4f, 0x682e6ff3,
        0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208, 0x90befffa, 0xa4506ceb, 0xbef9a3f7, 0xc67178f2
    };

    /**
     * Tinh ma bam SHA-256 theo tieu chuan FIPS 180-4.
     * Khong phu thuoc thu vien ben ngoai, dam bao tinh di dong tren moi nen tang C++.
     */
    string sha256(const string& input) {
        uint32_t H[8] = {
            0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a,
            0x510e527f, 0x9b05688c, 0x1f83d9ab, 0x5be0cd19
        };

        vector<uint8_t> msg(input.begin(), input.end());
        uint64_t bitLength = static_cast<uint64_t>(msg.size()) * 8;

        msg.push_back(0x80);
        while ((msg.size() % 64) != 56) {
            msg.push_back(0x00);
        }

        for (int i = 7; i >= 0; --i) {
            msg.push_back(static_cast<uint8_t>((bitLength >> (i * 8)) & 0xFF));
        }

        for (size_t chunk = 0; chunk < msg.size(); chunk += 64) {
            uint32_t W[64];
            for (int t = 0; t < 16; ++t) {
                W[t] = (static_cast<uint32_t>(msg[chunk + t * 4]) << 24) |
                       (static_cast<uint32_t>(msg[chunk + t * 4 + 1]) << 16) |
                       (static_cast<uint32_t>(msg[chunk + t * 4 + 2]) << 8) |
                       (static_cast<uint32_t>(msg[chunk + t * 4 + 3]));
            }
            for (int t = 16; t < 64; ++t) {
                W[t] = theta1(W[t - 2]) + W[t - 7] + theta0(W[t - 15]) + W[t - 16];
            }

            uint32_t a = H[0], b = H[1], c = H[2], d = H[3];
            uint32_t e = H[4], f = H[5], g = H[6], h = H[7];

            for (int t = 0; t < 64; ++t) {
                uint32_t T1 = h + sig1(e) + choose(e, f, g) + K[t] + W[t];
                uint32_t T2 = sig0(a) + majority(a, b, c);
                h = g;
                g = f;
                f = e;
                e = d + T1;
                d = c;
                c = b;
                b = a;
                a = T1 + T2;
            }

            H[0] += a; H[1] += b; H[2] += c; H[3] += d;
            H[4] += e; H[5] += f; H[6] += g; H[7] += h;
        }

        ostringstream oss;
        for (int i = 0; i < 8; ++i) {
            oss << hex << setfill('0') << setw(8) << H[i];
        }
        return oss.str();
    }

    // Tao chuoi salt ngau nhien cho moi tai khoan
    string taoSaltNgauNhien(size_t len = 12) {
        static const char chars[] =
            "0123456789ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz";
        random_device rd;
        mt19937 gen(rd());
        uniform_int_distribution<> dis(0, sizeof(chars) - 2);

        string s = "";
        for (size_t i = 0; i < len; ++i) {
            s += chars[dis(gen)];
        }
        return s;
    }

    // Ham bam ket hop Salt de ngan chan tan cong Rainbow Table
    string bamVoiSalt(const string& secret, const string& salt) {
        return sha256(salt + "$" + secret + "$" + salt);
    }
}

// ============================================================================
// CAC TIEN ICH KIEM TRA VA DINH DANG DU LIEU
// ============================================================================

// Kiem tra so double co huu han, khong phai NaN hay vo cuc (giu lai tu ban goc)
bool laSoHuuHan(double x) {
    return x == x &&
           x <= numeric_limits<double>::max() &&
           x >= -numeric_limits<double>::max();
}

// ============================================================================
// MODULE GIAO DIEN CONSOLE (UI & STYLING CHO LAUDAITINHAI BANK)
// ============================================================================
static bool g_useColor = true;

namespace UI {
    inline string reset()   { return g_useColor ? "\033[0m" : ""; }
    inline string bold()    { return g_useColor ? "\033[1m" : ""; }
    inline string dim()     { return g_useColor ? "\033[2m" : ""; }
    inline string blue()    { return g_useColor ? "\033[1;34m" : ""; }
    inline string cyan()    { return g_useColor ? "\033[1;36m" : ""; }
    inline string green()   { return g_useColor ? "\033[1;32m" : ""; }
    inline string red()     { return g_useColor ? "\033[1;31m" : ""; }
    inline string yellow()  { return g_useColor ? "\033[1;33m" : ""; }
    inline string white()   { return g_useColor ? "\033[1;37m" : ""; }
    inline string gray()    { return g_useColor ? "\033[90m" : ""; }

    inline void initConsole() {
#ifdef _WIN32
        if (!_isatty(_fileno(stdout))) {
            g_useColor = false;
            return;
        }
        HANDLE hOut = GetStdHandle(STD_OUTPUT_HANDLE);
        if (hOut != INVALID_HANDLE_VALUE) {
            DWORD dwMode = 0;
            if (GetConsoleMode(hOut, &dwMode)) {
                SetConsoleMode(hOut, dwMode | ENABLE_VIRTUAL_TERMINAL_PROCESSING);
            }
        }
        SetConsoleOutputCP(CP_UTF8);
#else
        if (!isatty(fileno(stdout))) {
            g_useColor = false;
        }
#endif
    }
}

// Dinh dang so tien voi dau phan cach hang nghin (VD: 1,250,000 VND hoac 802,987.50 VND)
string formatMoney(double amount, bool alwaysShowCents = false, const string& unit = "VND") {
    if (!laSoHuuHan(amount)) return "0 " + unit;
    bool negative = (amount < 0);
    double absAmount = std::abs(amount);
    long long integerPart = static_cast<long long>(absAmount);
    long long cents = static_cast<long long>(std::round((absAmount - integerPart) * 100.0));
    if (cents >= 100) {
        integerPart += 1;
        cents -= 100;
    }
    string intStr = to_string(integerPart);
    string formattedInt = "";
    int len = static_cast<int>(intStr.length());
    for (int i = 0; i < len; ++i) {
        if (i > 0 && (len - i) % 3 == 0) {
            formattedInt += ',';
        }
        formattedInt += intStr[i];
    }
    string result = (negative ? "-" : "") + formattedInt;
    if (cents > 0 || alwaysShowCents) {
        ostringstream oss;
        oss << "." << setfill('0') << setw(2) << cents;
        result += oss.str();
    }
    if (!unit.empty()) {
        result += " " + unit;
    }
    return result;
}

// Xoa man hinh console khi chuyen giua cac menu
void clearScreen() {
#ifdef _WIN32
    if (!_isatty(_fileno(stdout))) return;
#else
    if (!isatty(fileno(stdout))) return;
#endif
    if (g_useColor) {
        cout << "\033[2J\033[H" << flush;
    }
}

// Duong ke phan cach giao dien
void printDivider(int width = 72, char ch = '-') {
    cout << UI::cyan() << string(width, ch) << UI::reset() << "\n";
}

// Banner tieu de cua ngan hang BANK
void printBanner(const string& title, const string& subtitle = "") {
    int width = 72;
    cout << "\n" << UI::blue() << string(width, '=') << UI::reset() << "\n";
    string bankName = "LAUDAITINHAI BANK - HE THONG NGAN HANG SO";
    int padBank = (width - static_cast<int>(bankName.length())) / 2;
    if (padBank < 0) padBank = 0;
    cout << string(padBank, ' ') << UI::bold() << UI::white() << bankName << UI::reset() << "\n";

    if (!title.empty()) {
        int padTitle = (width - static_cast<int>(title.length())) / 2;
        if (padTitle < 0) padTitle = 0;
        cout << string(padTitle, ' ') << UI::cyan() << title << UI::reset() << "\n";
    }

    if (!subtitle.empty()) {
        int padSub = (width - static_cast<int>(subtitle.length())) / 2;
        if (padSub < 0) padSub = 0;
        cout << string(padSub, ' ') << UI::dim() << subtitle << UI::reset() << "\n";
    }
    cout << UI::blue() << string(width, '=') << UI::reset() << "\n";
}

// Thong bao trang thai
void showSuccess(const string& msg) {
    cout << UI::green() << "[THANH CONG]: " << msg << UI::reset() << "\n";
}

void showError(const string& msg) {
    cout << UI::red() << "[LOI]: " << msg << UI::reset() << "\n";
}

void showWarning(const string& msg) {
    cout << UI::yellow() << "[CANH BAO]: " << msg << UI::reset() << "\n";
}

void showInfo(const string& msg) {
    cout << UI::cyan() << "[THONG BAO]: " << msg << UI::reset() << "\n";
}

// Dung man hinh de nguoi dung kip doc thong tin truoc khi xoa
void pauseScreen() {
#ifdef _WIN32
    if (!_isatty(_fileno(stdin))) return;
    cout << "\n" << UI::dim() << ">> Nhan Enter de tiep tuc..." << UI::reset() << flush;
    while (true) {
        int ch = _getch();
        if (ch == 13 || ch == 10 || ch == 3 || ch == 26) break;
    }
#else
    if (!isatty(fileno(stdin))) return;
    cout << "\n>> Nhan Enter de tiep tuc..." << flush;
    string dummy;
    getline(cin, dummy);
#endif
}

// Lay thoi gian hien tai dinh dang chuoi "YYYY-MM-DD HH:MM:SS"
string layThoiGianHienTai() {
    auto now = chrono::system_clock::now();
    time_t t = chrono::system_clock::to_time_t(now);
    tm tmBuf;
#if defined(_WIN32) || defined(_WIN64)
    localtime_s(&tmBuf, &t);
#else
    localtime_r(&t, &tmBuf);
#endif
    char buf[64];
    strftime(buf, sizeof(buf), "%Y-%m-%d %H:%M:%S", &tmBuf);
    return string(buf);
}

// Lay ngay hien tai dinh dang "YYYY-MM-DD" dung de reset han muc ngay
string layNgayHienTai() {
    auto now = chrono::system_clock::now();
    time_t t = chrono::system_clock::to_time_t(now);
    tm tmBuf;
#if defined(_WIN32) || defined(_WIN64)
    localtime_s(&tmBuf, &t);
#else
    localtime_r(&t, &tmBuf);
#endif
    char buf[32];
    strftime(buf, sizeof(buf), "%Y-%m-%d", &tmBuf);
    return string(buf);
}

// Tao ma giao dich duy nhat dua tren thoi gian va bo dem
string taoMaGiaoDich() {
    static int counter = 1000;
    auto now = chrono::system_clock::now();
    time_t t = chrono::system_clock::to_time_t(now);
    tm tmBuf;
#if defined(_WIN32) || defined(_WIN64)
    localtime_s(&tmBuf, &t);
#else
    localtime_r(&t, &tmBuf);
#endif
    char buf[64];
    strftime(buf, sizeof(buf), "%Y%m%d%H%M%S", &tmBuf);
    counter = (counter + 1) % 9000 + 1000;
    return "GD" + string(buf) + "_" + to_string(counter);
}

// Kiem tra tinh hop le cua ma PIN (phai dung 6 chu so)
bool laPINHopLe(const string& pin) {
    if (pin.length() != BankConstants::DO_DAI_PIN_YEU_CAU) return false;
    for (char c : pin) {
        if (!isdigit(static_cast<unsigned char>(c))) return false;
    }
    return true;
}

// ============================================================================
// ENUM TRANG THAI TAI KHOAN VA LOAI GIAO DICH
// ============================================================================
enum class TrangThaiTaiKhoan {
    ACTIVE,  // Hoat dong binh thuong
    LOCKED,  // Bi khoa (do sai MK/PIN hoac do Admin khoa)
    CLOSED   // Da dong vinh vien
};

inline string trangThaiToString(TrangThaiTaiKhoan tt) {
    switch (tt) {
        case TrangThaiTaiKhoan::ACTIVE: return "Hoat dong";
        case TrangThaiTaiKhoan::LOCKED: return "Bi khoa";
        case TrangThaiTaiKhoan::CLOSED: return "Da dong";
        default: return "Khong xac dinh";
    }
}

enum class LoaiGiaoDich {
    NAP_TIEN,
    RUT_TIEN,
    CHUYEN_TIEN_DI,
    CHUYEN_TIEN_DEN,
    CONG_LAI
};

inline string loaiGDToString(LoaiGiaoDich loai) {
    switch (loai) {
        case LoaiGiaoDich::NAP_TIEN:         return "Nap tien";
        case LoaiGiaoDich::RUT_TIEN:         return "Rut tien";
        case LoaiGiaoDich::CHUYEN_TIEN_DI:   return "Chuyen tien di";
        case LoaiGiaoDich::CHUYEN_TIEN_DEN:  return "Nhan tien chuyen den";
        case LoaiGiaoDich::CONG_LAI:         return "Cong lai tiet kiem";
        default: return "Khac";
    }
}

// ============================================================================
// LOP GIAO DICH (TRANSACTION)
// ============================================================================
class GiaoDich {
private:
    string maGiaoDich;
    LoaiGiaoDich loai;
    string soTaiKhoanNguon;
    string soTaiKhoanDich;
    double soTien;
    double phiGiaoDich;
    string thoiGian;
    double soDuTruoc;
    double soDuSau;
    string trangThai; // "THANH_CONG", "THAT_BAI"
    string noiDung;

public:
    GiaoDich(string maGD = "",
             LoaiGiaoDich l = LoaiGiaoDich::NAP_TIEN,
             string nguon = "",
             string dich = "",
             double tien = 0.0,
             double phi = 0.0,
             string tg = "",
             double truoc = 0.0,
             double sau = 0.0,
             string tt = "THANH_CONG",
             string nd = "")
        : maGiaoDich(maGD), loai(l), soTaiKhoanNguon(nguon), soTaiKhoanDich(dich),
          soTien(tien), phiGiaoDich(phi), thoiGian(tg), soDuTruoc(truoc),
          soDuSau(sau), trangThai(tt), noiDung(nd) {
        if (thoiGian.empty()) {
            thoiGian = layThoiGianHienTai();
        }
        if (maGiaoDich.empty()) {
            maGiaoDich = taoMaGiaoDich();
        }
    }

    // Getters doc du lieu (khong co setter de bao dam tinh bat bien)
    string getMaGiaoDich() const { return maGiaoDich; }
    LoaiGiaoDich getLoai() const { return loai; }
    string getSoTaiKhoanNguon() const { return soTaiKhoanNguon; }
    string getSoTaiKhoanDich() const { return soTaiKhoanDich; }
    double getSoTien() const { return soTien; }
    double getPhiGiaoDich() const { return phiGiaoDich; }
    string getThoiGian() const { return thoiGian; }
    double getSoDuTruoc() const { return soDuTruoc; }
    double getSoDuSau() const { return soDuSau; }
    string getTrangThai() const { return trangThai; }
    string getNoiDung() const { return noiDung; }

    // Dinh dang hien thi dong bang sao ke
    void InDongBang() const {
        cout << left << setw(24) << maGiaoDich
             << setw(20) << thoiGian
             << setw(20) << loaiGDToString(loai)
             << right << setw(18) << formatMoney(soTien)
             << setw(14) << formatMoney(phiGiaoDich)
             << setw(18) << formatMoney(soDuSau) << "\n";
    }

    // Chuyen thanh dong CSV de xuat file
    string toCSV() const {
        ostringstream oss;
        oss << maGiaoDich << ","
            << "\"" << thoiGian << "\","
            << "\"" << loaiGDToString(loai) << "\","
            << soTaiKhoanNguon << ","
            << soTaiKhoanDich << ","
            << fixed << setprecision(2) << soTien << ","
            << phiGiaoDich << ","
            << soDuTruoc << ","
            << soDuSau << ","
            << "\"" << trangThai << "\","
            << "\"" << noiDung << "\"";
        return oss.str();
    }

    // Nap chong toan tu xuat
    friend ostream& operator<<(ostream& out, const GiaoDich& gd) {
        out << "------------------------------------------------------------\n"
            << "Ma GD:         " << gd.maGiaoDich << "\n"
            << "Thoi gian:     " << gd.thoiGian << "\n"
            << "Loai GD:       " << loaiGDToString(gd.loai) << "\n"
            << "TK Nguon:      " << gd.soTaiKhoanNguon << "\n";
        if (!gd.soTaiKhoanDich.empty()) {
            out << "TK Nhan:       " << gd.soTaiKhoanDich << "\n";
        }
        out << "So tien:       " << formatMoney(gd.soTien) << "\n"
            << "Phi giao dich: " << formatMoney(gd.phiGiaoDich) << "\n"
            << "So du truoc:   " << formatMoney(gd.soDuTruoc) << "\n"
            << "So du sau:     " << formatMoney(gd.soDuSau) << "\n"
            << "Trang thai:    " << gd.trangThai << "\n";
        if (!gd.noiDung.empty()) {
            out << "Noi dung:      " << gd.noiDung << "\n";
        }
        out << "------------------------------------------------------------\n";
        return out;
    }
};

// ============================================================================
// HAM NHAP DU LIEU NHAY CAM AN TOAN (AN KY TU BANG '*')
// Ho tro Windows (_getch tu <conio.h>) va POSIX (termios)
// ============================================================================
string NhapMatKhauAnToan(const string& prompt, size_t maxLen = 64,
                         bool chiChuSo = false, size_t doDaiCoDinh = 0) {
    while (true) {
        cout << prompt << flush;
        string res = "";

#ifdef _WIN32
        if (!_isatty(_fileno(stdin))) {
            // Khi du lieu vao qua pipe/file (test automation hoac redirection)
            if (!getline(cin, res)) return "";
            if (!res.empty() && res.back() == '\r') res.pop_back();
        } else {
            // Chay tuong tac truc tiep tren console Windows
            while (true) {
                int ch = _getch();

                // 1. Xu ly ma mo rong (phim mui ten, F1-F12, Insert, Delete, Home, End, PageUp, PageDown)
                if (ch == 0 || ch == 224) {
                    int ext = _getch(); // Doc ma scan code tiep theo va loai bo
                    (void)ext;
                    continue;
                }

                // 2. Phim Enter ket thuc nhap (\r hoac \n)
                if (ch == 13 || ch == 10) {
                    cout << "\n";
                    break;
                }

                // 3. Phim Backspace: xoa ky tu cuoi khoi bo dem va xoa '*' tren man hinh
                if (ch == 8) {
                    if (!res.empty()) {
                        res.pop_back();
                        cout << "\b \b" << flush;
                    }
                    continue;
                }

                // 4. Phim Ctrl+C (3) hoac Ctrl+Z (26 - EOF tren Windows)
                if (ch == 3 || ch == 26) {
                    cout << "\n";
                    return "";
                }

                // 5. Bo qua cac phim dieu khien khac (ch < 32 hoac ch > 126)
                if (ch < 32 || ch > 126) {
                    continue;
                }

                // 6. Neu yeu cau chi chu so (ma PIN) ma nhan phim khac thi bo qua
                if (chiChuSo && !isdigit(static_cast<unsigned char>(ch))) {
                    continue;
                }

                // 7. Kiem tra do dai toi da
                if (res.length() < maxLen) {
                    res.push_back(static_cast<char>(ch));
                    cout << '*' << flush;
                }
            }
        }
#endif

        // Kiem tra chuoi rong
        if (res.empty()) {
            if (cin.eof() || cin.fail()) return "";
            cout << "[Loi]: Du lieu khong duoc de trong! Vui long nhap lai.\n";
            continue;
        }

        // Kiem tra do dai co dinh neu co (vi du ma PIN)
        if (doDaiCoDinh > 0 && res.length() != doDaiCoDinh) {
            cout << "[Loi]: Do dai bat buoc phai dung " << doDaiCoDinh
                 << " chu so! Vui long nhap lai.\n";
            continue;
        }

        // Kiem tra PIN chi chua chu so (trong truong hop input qua pipe/file)
        if (chiChuSo && !laPINHopLe(res)) {
            cout << "[Loi]: Ma PIN phai la chuoi gom dung " << doDaiCoDinh
                 << " chu so! Vui long nhap lai.\n";
            continue;
        }

        return res;
    }
}

// ============================================================================
// LOP CO SO TRUU TUONG: TAI KHOAN
// ============================================================================
class TaiKhoan {
private:
    string soTaiKhoan;
    string tenChuTaiKhoan;
    double soDu;

    // Cac thuoc tinh bao mat & xac thuc (dong goi chat che)
    string matKhauHash;
    string pinHash;
    string salt;
    TrangThaiTaiKhoan trangThai;
    int soLanDangNhapSai;
    int soLanNhapPinSai;

    // Quan ly han muc ngay & canh bao
    double nguongCanhBaoSoDu;
    double tongRutTrongNgay;
    string ngayGiaoDichHienTai;

    // Nhat ky lich su giao dich rieng cua tai khoan
    vector<GiaoDich> lichSuGiaoDich;

protected:
    // Cho phep lop dan xuat truy cap va cap nhat so du co kiem soat
    double getSoDu() const {
        return soDu;
    }

    void setSoDu(double soDuMoi) {
        if (!laSoHuuHan(soDuMoi))
            throw invalid_argument("So du khong hop le!");
        soDu = soDuMoi;
    }

    // Nhap thong tin chung co ban
    void NhapThongTinChung(istream& in) {
        cout << "Nhap so tai khoan: ";
        getline(in, soTaiKhoan);
        if (soTaiKhoan.empty()) {
            throw invalid_argument("So tai khoan khong duoc de trong!");
        }

        cout << "Nhap ten chu tai khoan: ";
        getline(in, tenChuTaiKhoan);
        if (tenChuTaiKhoan.empty()) {
            throw invalid_argument("Ten chu tai khoan khong duoc de trong!");
        }

        cout << "Nhap so du ban dau (VND): ";
        string sSoDu;
        if (!(in >> sSoDu)) {
            in.clear();
            in.ignore(numeric_limits<streamsize>::max(), '\n');
            throw invalid_argument("So du phai la mot con so hop le!");
        }
        in.ignore(numeric_limits<streamsize>::max(), '\n');

        string cleanSoDu = "";
        for (char c : sSoDu) {
            if (c != ',') cleanSoDu += c;
        }

        try {
            size_t idx = 0;
            soDu = stod(cleanSoDu, &idx);
            if (idx != cleanSoDu.length() || !laSoHuuHan(soDu) || soDu < 0) {
                throw invalid_argument("So du ban dau phai >= 0 va la so thuc huu han!");
            }
        } catch (const invalid_argument&) {
            throw;
        } catch (...) {
            throw invalid_argument("So du phai la mot con so hop le!");
        }
    }

    // Phuong thuc ao thuan tuy de lop con nhap thuoc tinh rieng
    virtual void NhapThuocTinhRieng(istream& in) = 0;

    // Nhap thong tin xac thuc bao mat (Mat khau va PIN) - Co che an ky tu bang '*'
    void NhapThongTinBaoMat(istream& in) {
        (void)in;
        string mk = NhapMatKhauAnToan("Thiet lap mat khau dang nhap: ", 32);
        string xnMK = NhapMatKhauAnToan("Xac nhan mat khau: ", 32);
        if (mk != xnMK) {
            throw invalid_argument("Xac nhan mat khau khong khop!");
        }

        string pin = NhapMatKhauAnToan("Thiet lap ma PIN giao dich (gom 6 chu so): ",
                                       BankConstants::DO_DAI_PIN_YEU_CAU, true,
                                       BankConstants::DO_DAI_PIN_YEU_CAU);
        string xnPin = NhapMatKhauAnToan("Xac nhan ma PIN: ",
                                         BankConstants::DO_DAI_PIN_YEU_CAU, true,
                                         BankConstants::DO_DAI_PIN_YEU_CAU);
        if (pin != xnPin) {
            throw invalid_argument("Xac nhan ma PIN khong khop!");
        }

        if (pin == mk) {
            throw invalid_argument("Ma PIN va mat khau phai doc lap, khong duoc trung nhau!");
        }

        // Bam va luu tru bao mat
        DatMatKhauVaPIN(mk, pin);
    }

    // Template Method: Quy dinh trinh tu nhap thong tin tai khoan chuan xac theo de bai:
    // 1. Thong tin chung (So TK, Ten, So du)
    // 2. Thuoc tinh rieng cua tung loai tai khoan
    // 3. Thong tin bao mat (Mat khau, PIN)
    virtual void NhapThongTin(istream& in) {
        NhapThongTinChung(in);
        NhapThuocTinhRieng(in);
        NhapThongTinBaoMat(in);
    }

    // Xuat thong tin tong quan (TUYET DOI KHONG XUAT MAT KHAU / PIN)
    virtual void XuatThongTinChung(ostream& out) const {
        out << "  Ngan hang:          LAUDAITINHAI BANK\n";
        out << "  So tai khoan:       " << soTaiKhoan << '\n';
        out << "  Chu tai khoan:      " << tenChuTaiKhoan << '\n';
        out << "  Trang thai:         " << trangThaiToString(trangThai) << '\n';
        out << "  So du thuc te:      " << formatMoney(soDu) << '\n';
        out << "  So du kha dung:     " << formatMoney(getSoDuKhaDung()) << '\n';
        out << "  Nguong canh bao:    " << formatMoney(nguongCanhBaoSoDu) << '\n';
        out << "  Rut hom nay:        " << formatMoney(tongRutTrongNgay) << " / "
            << formatMoney(BankConstants::HAN_MUC_RUT_NGAY_TOI_DA) << '\n';
    }

    virtual void XuatThuocTinhRieng(ostream& out) const = 0;

    virtual void XuatThongTin(ostream& out) const {
        out << "------------------ THONG TIN TAI KHOAN ------------------\n";
        out << "  Loai tai khoan:     " << getLoaiTaiKhoan() << '\n';
        XuatThongTinChung(out);
        XuatThuocTinhRieng(out);
        out << "---------------------------------------------------------\n";
    }

    // Kiem tra va cap nhat han muc rut tien trong ngay
    bool KiemTraHanMucNgay(double soTien, string& lyDo) {
        string ngayNay = layNgayHienTai();
        if (ngayGiaoDichHienTai != ngayNay) {
            ngayGiaoDichHienTai = ngayNay;
            tongRutTrongNgay = 0.0;
        }

        if (soTien < BankConstants::HAN_MUC_RUT_MOI_LAN_TOI_THIEU) {
            lyDo = "So tien rut moi lan toi thieu la " +
                   formatMoney(BankConstants::HAN_MUC_RUT_MOI_LAN_TOI_THIEU) + "!";
            return false;
        }

        if (soTien > BankConstants::HAN_MUC_RUT_MOI_LAN_TOI_DA) {
            lyDo = "So tien rut vuot qua han muc 1 lan (toi da " +
                   formatMoney(BankConstants::HAN_MUC_RUT_MOI_LAN_TOI_DA) + ")!";
            return false;
        }

        if (tongRutTrongNgay + soTien > BankConstants::HAN_MUC_RUT_NGAY_TOI_DA) {
            lyDo = "Vuot qua tong han muc rut trong ngay (con lai: " +
                   formatMoney(BankConstants::HAN_MUC_RUT_NGAY_TOI_DA - tongRutTrongNgay) + ")!";
            return false;
        }

        return true;
    }

    void GhiNhanRutTrongNgay(double soTien) {
        string ngayNay = layNgayHienTai();
        if (ngayGiaoDichHienTai != ngayNay) {
            ngayGiaoDichHienTai = ngayNay;
            tongRutTrongNgay = 0.0;
        }
        tongRutTrongNgay += soTien;
    }

    // Cac phuong thuc rut tien va nap tien cot loi duoc de o protected
    // de ngan chan viec bo qua buoc xac thuc PIN tu ben ngoai
    virtual bool RutTien(double soTien) = 0;

    virtual bool NapTien(double soTien) {
        if (!laSoHuuHan(soTien) || soTien <= 0)
            return false;
        if (soDu > numeric_limits<double>::max() - soTien)
            return false;
        soDu += soTien;
        return true;
    }

public:
    // Constructor khoi tao
    TaiKhoan(string soTK = "", string ten = "", double sd = 0)
        : soTaiKhoan(soTK), tenChuTaiKhoan(ten), soDu(sd),
          trangThai(TrangThaiTaiKhoan::ACTIVE),
          soLanDangNhapSai(0), soLanNhapPinSai(0),
          nguongCanhBaoSoDu(BankConstants::NGUONG_CANH_BAO_MAC_DINH),
          tongRutTrongNgay(0.0), ngayGiaoDichHienTai(layNgayHienTai()) {
        if (!laSoHuuHan(sd))
            throw invalid_argument("So du khoi tao phai la so thuc huu han!");
        salt = Security::taoSaltNgauNhien();
    }

    // Virtual destructor dam bao huy an toan lop con
    virtual ~TaiKhoan() = default;

    // Getters
    string getSoTaiKhoan() const { return soTaiKhoan; }
    string getTenChuTaiKhoan() const { return tenChuTaiKhoan; }
    TrangThaiTaiKhoan getTrangThai() const { return trangThai; }
    string getTrangThaiString() const { return trangThaiToString(trangThai); }
    double getNguongCanhBao() const { return nguongCanhBaoSoDu; }
    const vector<GiaoDich>& getLichSuGiaoDich() const { return lichSuGiaoDich; }
    string getSalt() const { return salt; }
    string getMatKhauHash() const { return matKhauHash; }
    string getPinHash() const { return pinHash; }
    int getSoLanDangNhapSai() const { return soLanDangNhapSai; }
    int getSoLanNhapPinSai() const { return soLanNhapPinSai; }

    // Setters
    void setSoTaiKhoan(const string& soTK) {
        if (soTK.empty()) throw invalid_argument("So tai khoan khong duoc rong!");
        soTaiKhoan = soTK;
    }

    void setTenChuTaiKhoan(const string& ten) {
        if (ten.empty()) throw invalid_argument("Ten chu tai khoan khong duoc rong!");
        tenChuTaiKhoan = ten;
    }

    void setNguongCanhBao(double nguong) {
        if (!laSoHuuHan(nguong) || nguong < 0)
            throw invalid_argument("Nguong canh bao phai >= 0!");
        nguongCanhBaoSoDu = nguong;
    }

    void setTrangThai(TrangThaiTaiKhoan tt) {
        trangThai = tt;
    }

    double getSoDuCongKhai() const {
        return soDu;
    }

    // ==================== QUAN LY XAC THUC & MAT KHAU / PIN ====================

    void DatMatKhauVaPIN(const string& mk, const string& pin) {
        if (salt.empty()) {
            salt = Security::taoSaltNgauNhien();
        }
        matKhauHash = Security::bamVoiSalt(mk, salt);
        pinHash = Security::bamVoiSalt(pin, salt);
        soLanDangNhapSai = 0;
        soLanNhapPinSai = 0;
    }

    // Phuong thuc phuc vu viec tai du lieu tu file luu tru
    void NapThongTinBaoMatTuFile(const string& s, const string& mkH, const string& pinH,
                                TrangThaiTaiKhoan tt, int saiMK, int saiPIN,
                                double nguong, double rutNgay, const string& ngayGD) {
        salt = s;
        matKhauHash = mkH;
        pinHash = pinH;
        trangThai = tt;
        soLanDangNhapSai = saiMK;
        soLanNhapPinSai = saiPIN;
        nguongCanhBaoSoDu = nguong;
        tongRutTrongNgay = rutNgay;
        ngayGiaoDichHienTai = ngayGD;
    }

    // Xac thuc mat khau khi dang nhap
    bool XacThucMatKhau(const string& mk, string& thongBaoLoi) {
        if (trangThai == TrangThaiTaiKhoan::CLOSED) {
            thongBaoLoi = "Tai khoan nay da bi dong!";
            return false;
        }
        if (trangThai == TrangThaiTaiKhoan::LOCKED) {
            thongBaoLoi = "Tai khoan dang bi khoa! Vui long lien he Quan tri vien de mo khoa.";
            return false;
        }

        string hashNhap = Security::bamVoiSalt(mk, salt);
        if (hashNhap == matKhauHash) {
            soLanDangNhapSai = 0; // Reset khi dung
            return true;
        }

        // Xu ly khi sai mat khau
        soLanDangNhapSai++;
        if (soLanDangNhapSai >= BankConstants::MAX_SAI_MAT_KHAU) {
            trangThai = TrangThaiTaiKhoan::LOCKED;
            thongBaoLoi = "Ban da nhap sai mat khau qua 5 lan. Tai khoan da bi KHOA!";
        } else {
            thongBaoLoi = "Thong tin dang nhap khong chinh xac! (Con " +
                          to_string(BankConstants::MAX_SAI_MAT_KHAU - soLanDangNhapSai) + " lan thu)";
        }
        return false;
    }

    // Xac thuc ma PIN giao dich
    bool XacThucPIN(const string& pin, string& thongBaoLoi) {
        if (trangThai == TrangThaiTaiKhoan::CLOSED) {
            thongBaoLoi = "Tai khoan da dong, khong the thuc hien giao dich!";
            return false;
        }
        if (trangThai == TrangThaiTaiKhoan::LOCKED) {
            thongBaoLoi = "Tai khoan dang bi khoa, khong the giao dich!";
            return false;
        }

        string hashNhap = Security::bamVoiSalt(pin, salt);
        if (hashNhap == pinHash) {
            soLanNhapPinSai = 0; // Reset khi dung
            return true;
        }

        soLanNhapPinSai++;
        if (soLanNhapPinSai >= BankConstants::MAX_SAI_PIN) {
            trangThai = TrangThaiTaiKhoan::LOCKED;
            thongBaoLoi = "Nhap sai ma PIN qua 3 lan! Tai khoan da bi KHOA de bao ve tai san.";
        } else {
            thongBaoLoi = "Ma PIN giao dich khong chinh xac! (Con " +
                          to_string(BankConstants::MAX_SAI_PIN - soLanNhapPinSai) + " lan thu)";
        }
        return false;
    }

    // Doi mat khau
    bool DoiMatKhau(const string& mkCu, const string& mkMoi, const string& xacNhanMoi, string& thongBao) {
        if (trangThai != TrangThaiTaiKhoan::ACTIVE) {
            thongBao = "Tai khoan khong o trang thai hoat dong de doi mat khau!";
            return false;
        }
        if (Security::bamVoiSalt(mkCu, salt) != matKhauHash) {
            thongBao = "Mat khau hien tai khong dung!";
            return false;
        }
        if (mkMoi.empty()) {
            thongBao = "Mat khau moi khong duoc de trong!";
            return false;
        }
        if (mkMoi != xacNhanMoi) {
            thongBao = "Xac nhan mat khau moi khong khop!";
            return false;
        }
        if (mkMoi == mkCu) {
            thongBao = "Mat khau moi phai khac mat khau hien tai!";
            return false;
        }

        // Cap nhat mat khau moi
        matKhauHash = Security::bamVoiSalt(mkMoi, salt);
        soLanDangNhapSai = 0;
        thongBao = "Doi mat khau dang nhap thanh cong!";
        return true;
    }

    // Doi ma PIN giao dich
    bool DoiPIN(const string& pinCu, const string& pinMoi, const string& xacNhanMoi, string& thongBao) {
        if (trangThai != TrangThaiTaiKhoan::ACTIVE) {
            thongBao = "Tai khoan khong o trang thai hoat dong de doi ma PIN!";
            return false;
        }
        if (Security::bamVoiSalt(pinCu, salt) != pinHash) {
            thongBao = "Ma PIN hien tai khong dung!";
            return false;
        }
        if (!laPINHopLe(pinMoi)) {
            thongBao = "Ma PIN moi phai gom dung 6 chu so!";
            return false;
        }
        if (pinMoi != xacNhanMoi) {
            thongBao = "Xac nhan ma PIN moi khong khop!";
            return false;
        }
        if (pinMoi == pinCu) {
            thongBao = "Ma PIN moi phai khac ma PIN hien tai!";
            return false;
        }

        pinHash = Security::bamVoiSalt(pinMoi, salt);
        soLanNhapPinSai = 0;
        thongBao = "Doi ma PIN giao dich thanh cong!";
        return true;
    }

    // Cac thao tac quan tri trang thai tai khoan
    void MoKhoa() {
        trangThai = TrangThaiTaiKhoan::ACTIVE;
        soLanDangNhapSai = 0;
        soLanNhapPinSai = 0;
    }

    void KhoaTaiKhoan() {
        trangThai = TrangThaiTaiKhoan::LOCKED;
    }

    void DongTaiKhoan() {
        trangThai = TrangThaiTaiKhoan::CLOSED;
    }

    // ==================== CAC PHUONG THUC DA HINH ====================
    virtual bool CoTheRut(double soTien, string& lyDo) const = 0;
    virtual double getSoDuKhaDung() const = 0;
    virtual void HienThiThongTin() const = 0;
    virtual string getLoaiTaiKhoan() const = 0;

    // ==================== NGHIEP VU GIAO DICH AN TOAN ====================

    // Nap tien an toan: Yeu cau xac thuc PIN, ghi nhat ky giao dich
    bool ThucHienNapTien(double soTien, const string& pin, string& lyDo) {
        if (trangThai != TrangThaiTaiKhoan::ACTIVE) {
            lyDo = "Tai khoan khong o trang thai hoat dong de nap tien!";
            return false;
        }
        if (!laSoHuuHan(soTien) || soTien <= 0) {
            lyDo = "So tien nap phai la so duong hop le!";
            return false;
        }
        if (soTien < 10000.0) {
            lyDo = "So tien nap toi thieu la 10,000 VND!";
            return false;
        }
        if (!XacThucPIN(pin, lyDo)) {
            return false; // Ly do sai PIN da duoc gan boi XacThucPIN
        }

        double truoc = soDu;
        if (!NapTien(soTien)) {
            lyDo = "Loi tran so du he thong!";
            return false;
        }
        double sau = soDu;

        // Ghi nhan lich su giao dich
        GiaoDich gd(taoMaGiaoDich(), LoaiGiaoDich::NAP_TIEN, soTaiKhoan, "",
                   soTien, 0.0, layThoiGianHienTai(), truoc, sau, "THANH_CONG", "Nap tien vao tai khoan");
        lichSuGiaoDich.push_back(gd);

        lyDo = "Nap tien thanh cong!";
        return true;
    }

    // Rut tien an toan: Yeu cau xac thuc PIN, kiem tra han muc ngay, da hinh rut
    bool ThucHienRutTien(double soTien, const string& pin, string& lyDo) {
        if (trangThai != TrangThaiTaiKhoan::ACTIVE) {
            lyDo = "Tai khoan khong o trang thai hoat dong de rut tien!";
            return false;
        }
        if (!laSoHuuHan(soTien) || soTien <= 0) {
            lyDo = "So tien rut phai la so duong hop le!";
            return false;
        }
        if (!KiemTraHanMucNgay(soTien, lyDo)) {
            return false;
        }
        if (!CoTheRut(soTien, lyDo)) {
            return false;
        }
        if (!XacThucPIN(pin, lyDo)) {
            return false;
        }

        double truoc = soDu;
        if (!RutTien(soTien)) {
            lyDo = "Giao dich rut tien that bai do loi he thong!";
            return false;
        }
        double sau = soDu;
        GhiNhanRutTrongNgay(soTien);

        // Ghi nhan lich su giao dich
        GiaoDich gd(taoMaGiaoDich(), LoaiGiaoDich::RUT_TIEN, soTaiKhoan, "",
                   soTien, 0.0, layThoiGianHienTai(), truoc, sau, "THANH_CONG", "Rut tien mat");
        lichSuGiaoDich.push_back(gd);

        lyDo = "Rut tien thanh cong!";
        // Kiem tra canh bao so du
        if (sau < nguongCanhBaoSoDu) {
            lyDo += "\n[CANH BAO]: So du con lai (" + formatMoney(sau) +
                    ") da xuong duoi nguong canh bao (" +
                    formatMoney(nguongCanhBaoSoDu) + ")!";
        }
        return true;
    }

    // Them truc tiep mot ban ghi giao dich (su dung trong chuyen tien / cong lai)
    void ThemGiaoDich(const GiaoDich& gd) {
        lichSuGiaoDich.push_back(gd);
    }

    // Xem toan bo lich su giao dich (sap xep thoi gian giam dan - moi nhat truoc)
    void HienThiLichSu() const {
        if (lichSuGiaoDich.empty()) {
            cout << UI::yellow() << "Tai khoan chua co giao dich nao duoc ghi nhan.\n" << UI::reset();
            return;
        }

        cout << "\n" << UI::blue() << string(114, '=') << UI::reset() << "\n";
        cout << UI::bold() << "                         LICH SU GIAO DICH TAI KHOAN: " << soTaiKhoan << UI::reset() << "\n";
        cout << UI::blue() << string(114, '=') << UI::reset() << "\n";
        cout << UI::cyan()
             << left << setw(24) << "MA GIAO DICH"
             << setw(20) << "THOI GIAN"
             << setw(20) << "LOAI GIAO DICH"
             << right << setw(18) << "SO TIEN"
             << setw(14) << "PHI"
             << setw(18) << "SO DU SAU"
             << UI::reset() << "\n";
        cout << string(114, '-') << "\n";

        // In nguoc tu cuoi ve dau de hien thi giao dich moi nhat truoc
        for (auto it = lichSuGiaoDich.rbegin(); it != lichSuGiaoDich.rend(); ++it) {
            it->InDongBang();
        }
        cout << UI::blue() << string(114, '=') << UI::reset() << "\n";
    }

    // Xem giao dich gan nhat
    void HienThiGiaoDichGanNhat() const {
        if (lichSuGiaoDich.empty()) {
            cout << UI::yellow() << "Chua co giao dich nao!\n" << UI::reset();
            return;
        }
        cout << "\n=== GIAO DICH GAN NHAT ===\n";
        cout << lichSuGiaoDich.back();
    }

    // Tim kiem giao dich theo ma
    bool TimGiaoDichTheoMa(const string& maGD, GiaoDich& outGD) const {
        for (const auto& gd : lichSuGiaoDich) {
            if (gd.getMaGiaoDich() == maGD) {
                outGD = gd;
                return true;
            }
        }
        return false;
    }

    // Loc giao dich theo loai
    void LocGiaoDichTheoLoai(LoaiGiaoDich loai) const {
        cout << "\n" << UI::cyan() << "=== DANH SACH GIAO DICH THEO LOAI: " << loaiGDToString(loai) << " ===" << UI::reset() << "\n";
        bool co = false;
        for (auto it = lichSuGiaoDich.rbegin(); it != lichSuGiaoDich.rend(); ++it) {
            if (it->getLoai() == loai) {
                if (!co) {
                    cout << UI::cyan()
                         << left << setw(24) << "MA GIAO DICH"
                         << setw(20) << "THOI GIAN"
                         << setw(20) << "LOAI GIAO DICH"
                         << right << setw(18) << "SO TIEN"
                         << setw(14) << "PHI"
                         << setw(18) << "SO DU SAU"
                         << UI::reset() << "\n";
                    cout << string(114, '-') << "\n";
                }
                it->InDongBang();
                co = true;
            }
        }
        if (!co) {
            cout << UI::yellow() << "Khong tim thay giao dich phu hop.\n" << UI::reset();
        } else {
            cout << string(114, '-') << "\n";
        }
    }

    // Xuat sao ke ra file TXT hoac CSV
    bool XuatSaoKe(const string& duongDan, bool laCSV) const {
        ofstream f(duongDan);
        if (!f.is_open()) return false;

        if (laCSV) {
            f << "MaGD,ThoiGian,LoaiGD,TKNguon,TKDich,SoTien,Phi,SoDuTruoc,SoDuSau,TrangThai,NoiDung\n";
            for (const auto& gd : lichSuGiaoDich) {
                f << gd.toCSV() << "\n";
            }
        } else {
            f << "================================================================================\n";
            f << "                       SAO KE TAI KHOAN NGAN HANG                               \n";
            f << "================================================================================\n";
            f << "So tai khoan:   " << soTaiKhoan << "\n";
            f << "Chu tai khoan:  " << tenChuTaiKhoan << "\n";
            f << "Loai tai khoan: " << getLoaiTaiKhoan() << "\n";
            f << "So du hien tai: " << formatMoney(soDu) << "\n";
            f << "Ngay in sao ke: " << layThoiGianHienTai() << "\n";
            f << "Tong so giao dich: " << lichSuGiaoDich.size() << "\n";
            f << "--------------------------------------------------------------------------------\n";
            for (const auto& gd : lichSuGiaoDich) {
                f << gd << "\n";
            }
            f << "================================================================================\n";
        }
        f.close();
        return true;
    }

    // Lop NganHang duoc phep thuc hien cac thao tac nguyen tu trong chuyen tien
    friend class NganHang;

    // Nap chong toan tu nhap / xuat
    friend istream& operator>>(istream& in, TaiKhoan& tk) {
        tk.NhapThongTin(in);
        return in;
    }

    friend ostream& operator<<(ostream& out, const TaiKhoan& tk) {
        tk.XuatThongTin(out);
        return out;
    }
};

// ============================================================================
// LOP DAN XUAT: TAI KHOAN TIET KIEM
// ============================================================================
class TaiKhoanTietKiem : public TaiKhoan {
private:
    double laiSuat; // Phan tram / nam (vi du 6.5%)

protected:
    void NhapThuocTinhRieng(istream& in) override {
        cout << "Nhap lai suat (%/nam, vi du 6.5): ";
        if (!(in >> laiSuat)) {
            in.clear();
            in.ignore(numeric_limits<streamsize>::max(), '\n');
            throw invalid_argument("Lai suat phai la mot con so hop le!");
        }
        in.ignore(numeric_limits<streamsize>::max(), '\n');

        if (!laSoHuuHan(laiSuat) || laiSuat < 0 || laiSuat > 10)
            throw invalid_argument("Lai suat phai tu 0 den 10%!");
    }

    void XuatThuocTinhRieng(ostream& out) const override {
        out << "  Lai suat tiet kiem: " << fixed << setprecision(2) << laiSuat << " %/nam\n";
        out << "  Tien lai 1 thang:   " << formatMoney(TinhLaiHangThang()) << " (uoc tinh)\n";
    }

public:
    TaiKhoanTietKiem(string soTK = "", string ten = "", double sd = 0, double ls = 0)
        : TaiKhoan(soTK, ten, sd), laiSuat(ls) {
        if (!laSoHuuHan(ls) || ls < 0 || ls > 10)
            throw invalid_argument("Lai suat khong hop le!");
        if (sd < 0)
            throw invalid_argument("Tai khoan tiet kiem khong duoc co so du am!");
    }

    double getLaiSuat() const { return laiSuat; }

    void setLaiSuat(double ls) {
        if (!laSoHuuHan(ls) || ls < 0 || ls > 10)
            throw invalid_argument("Lai suat phai tu 0 den 10%!");
        laiSuat = ls;
    }

    // Tai khoan tiet kiem khong duoc am so du
    bool CoTheRut(double soTien, string& lyDo) const override {
        if (!laSoHuuHan(soTien) || soTien <= 0) {
            lyDo = "So tien rut khong hop le!";
            return false;
        }
        if (soTien > getSoDu()) {
            lyDo = "So du khong du! Tai khoan tiet kiem khong cho phep rut vuot qua so du hien co.";
            return false;
        }
        return true;
    }

    double getSoDuKhaDung() const override {
        return getSoDu();
    }

    // Rut tien thuc te (da hinh)
    bool RutTien(double soTien) override {
        if (!laSoHuuHan(soTien) || soTien <= 0 || soTien > getSoDu())
            return false;

        setSoDu(getSoDu() - soTien);
        return true;
    }

    void HienThiThongTin() const override {
        cout << *this;
    }

    string getLoaiTaiKhoan() const override {
        return "Tiet kiem";
    }

    // Tinh tien lai 1 thang
    double TinhLaiHangThang() const {
        return getSoDu() * (laiSuat / 100.0) / 12.0;
    }

    // Ket toan va cong lai thang vao tai khoan
    bool CongLaiTietKiem(GiaoDich& outGD) {
        double tienLai = TinhLaiHangThang();
        if (tienLai <= 0) return false;

        double truoc = getSoDu();
        setSoDu(truoc + tienLai);
        double sau = getSoDu();

        outGD = GiaoDich(taoMaGiaoDich(), LoaiGiaoDich::CONG_LAI, "", getSoTaiKhoan(),
                         tienLai, 0.0, layThoiGianHienTai(), truoc, sau,
                         "THANH_CONG", "Ket toan lai tiet kiem hang thang (" + to_string(laiSuat) + "%/nam)");
        ThemGiaoDich(outGD);
        return true;
    }
};

// ============================================================================
// LOP DAN XUAT: TAI KHOAN THANH TOAN
// ============================================================================
class TaiKhoanThanhToan : public TaiKhoan {
private:
    double hanMucTinDung; // Cho phep so du am toi da trong han muc

protected:
    void NhapThuocTinhRieng(istream& in) override {
        cout << "Nhap han muc tin dung (VND, >= 0): ";
        string sHanMuc;
        if (!(in >> sHanMuc)) {
            in.clear();
            in.ignore(numeric_limits<streamsize>::max(), '\n');
            throw invalid_argument("Han muc tin dung phai la mot con so hop le!");
        }
        in.ignore(numeric_limits<streamsize>::max(), '\n');

        string cleanHanMuc = "";
        for (char c : sHanMuc) {
            if (c != ',') cleanHanMuc += c;
        }

        try {
            size_t idx = 0;
            hanMucTinDung = stod(cleanHanMuc, &idx);
            if (idx != cleanHanMuc.length() || !laSoHuuHan(hanMucTinDung) || hanMucTinDung < 0) {
                throw invalid_argument("Han muc tin dung phai >= 0 va la so thuc huu han!");
            }
        } catch (const invalid_argument&) {
            throw;
        } catch (...) {
            throw invalid_argument("Han muc tin dung phai la mot con so hop le!");
        }
    }

    void XuatThuocTinhRieng(ostream& out) const override {
        out << "  Han muc tin dung:   " << formatMoney(hanMucTinDung) << '\n';
        out << "  So tien co the chi: " << formatMoney(getSoDuKhaDung()) << '\n';
    }

public:
    TaiKhoanThanhToan(string soTK = "", string ten = "", double sd = 0, double hmt = 0)
        : TaiKhoan(soTK, ten, sd), hanMucTinDung(hmt) {
        if (!laSoHuuHan(hmt) || hmt < 0)
            throw invalid_argument("Han muc tin dung khong hop le!");
        if (sd < -hmt)
            throw invalid_argument("So du khong duoc vuot qua han muc tin dung!");
    }

    double getHanMucTinDung() const { return hanMucTinDung; }

    void setHanMucTinDung(double hmt) {
        if (!laSoHuuHan(hmt) || hmt < 0)
            throw invalid_argument("Han muc tin dung phai >= 0!");
        hanMucTinDung = hmt;
    }

    // Tai khoan thanh toan cho phep su dung ca han muc tin dung (so du am)
    bool CoTheRut(double soTien, string& lyDo) const override {
        if (!laSoHuuHan(soTien) || soTien <= 0) {
            lyDo = "So tien rut khong hop le!";
            return false;
        }
        if (soTien > getSoDu() + hanMucTinDung) {
            lyDo = "Vuot qua tong so du va han muc tin dung cho phep (Kha dung: " +
                   formatMoney(getSoDuKhaDung()) + ")!";
            return false;
        }
        return true;
    }

    double getSoDuKhaDung() const override {
        return getSoDu() + hanMucTinDung;
    }

    // Rut tien thuc te (da hinh)
    bool RutTien(double soTien) override {
        if (!laSoHuuHan(soTien) || soTien <= 0 || soTien > getSoDu() + hanMucTinDung)
            return false;

        setSoDu(getSoDu() - soTien);
        return true;
    }

    void HienThiThongTin() const override {
        cout << *this;
    }

    string getLoaiTaiKhoan() const override {
        return "Thanh toan";
    }
};

// ============================================================================
// LOP QUAN LY NGAN HANG (BANK MANAGER)
// Dieu phoi toan bo danh sach tai khoan, giao dich chuyen tien nguyen tu,
// bao mat admin, bao cao thong ke va luu tru file.
// ============================================================================
class NganHang {
private:
    vector<unique_ptr<TaiKhoan>> danhSachTaiKhoan;

    // Tai khoan quan tri vien he thong (Demo Admin)
    string adminUsername;
    string adminPasswordHash;
    string adminSalt;

public:
    NganHang() {
        adminUsername = "admin";
        adminSalt = "BankSystem@2026";
        // Mat khau mac dinh cua admin la "admin123"
        adminPasswordHash = Security::bamVoiSalt("admin123", adminSalt);
    }

    // Xac thuc quyen quan tri vien
    bool XacThucAdmin(const string& user, const string& pass) const {
        if (user != adminUsername) return false;
        return Security::bamVoiSalt(pass, adminSalt) == adminPasswordHash;
    }

    // Tim vi tri tai khoan theo so tai khoan (chinh xac)
    int TimTaiKhoanTheoSoTK(const string& soTK) const {
        for (int i = 0; i < static_cast<int>(danhSachTaiKhoan.size()); ++i) {
            if (danhSachTaiKhoan[i]->getSoTaiKhoan() == soTK)
                return i;
        }
        return -1;
    }

    TaiKhoan* getTaiKhoanPtr(const string& soTK) {
        int idx = TimTaiKhoanTheoSoTK(soTK);
        if (idx != -1) return danhSachTaiKhoan[idx].get();
        return nullptr;
    }

    const TaiKhoan* getTaiKhoanPtr(const string& soTK) const {
        int idx = TimTaiKhoanTheoSoTK(soTK);
        if (idx != -1) return danhSachTaiKhoan[idx].get();
        return nullptr;
    }

    // Them tai khoan moi vao ngan hang
    bool ThemTaiKhoan(unique_ptr<TaiKhoan> tk, string& lyDo) {
        if (!tk) {
            lyDo = "Tai khoan khong hop le!";
            return false;
        }
        if (TimTaiKhoanTheoSoTK(tk->getSoTaiKhoan()) != -1) {
            lyDo = "So tai khoan nay da ton tai trong he thong!";
            return false;
        }
        danhSachTaiKhoan.push_back(move(tk));
        lyDo = "Dang ky mo tai khoan moi thanh cong!";
        return true;
    }

    // Dang nhap tai khoan khach hang
    TaiKhoan* DangNhap(const string& soTK, const string& matKhau, string& thongBaoLoi) {
        int idx = TimTaiKhoanTheoSoTK(soTK);
        if (idx == -1) {
            thongBaoLoi = "So tai khoan hoac mat khau khong chinh xac!";
            return nullptr;
        }

        TaiKhoan* tk = danhSachTaiKhoan[idx].get();
        if (tk->XacThucMatKhau(matKhau, thongBaoLoi)) {
            return tk;
        }
        return nullptr;
    }

    // ==================== GIAO DICH CHUYEN TIEN NGUYEN TU ====================
    /**
     * Chuyen tien giua 2 tai khoan voi tinh nhat quan tuyet doi (Atomic):
     * 1. Kiem tra tai khoan nguon va dich ton tai, khac nhau, dang ACTIVE.
     * 2. Xac thuc ma PIN cua tai khoan nguon.
     * 3. Tinh phi chuyen tien ro rang (2.000 VND).
     * 4. Kiem tra kha nang chi tra cua nguon (so tien + phi).
     * 5. Kiem tra kha nang tiep nhan cua dich.
     * 6. Chi khi tat ca deu dat moi cap nhat so du ca hai ben.
     * 7. Ghi nhat ky giao dich dong bo cho ca hai tai khoan.
     */
    bool ChuyenTien(const string& soTKNguon, const string& soTKDich,
                    double soTien, const string& pin, string& lyDo) {
        if (soTKNguon == soTKDich) {
            lyDo = "Tai khoan nhan phai khac tai khoan chuyen!";
            return false;
        }

        int idxNguon = TimTaiKhoanTheoSoTK(soTKNguon);
        int idxDich = TimTaiKhoanTheoSoTK(soTKDich);

        if (idxNguon == -1) {
            lyDo = "Khong tim thay tai khoan nguon!";
            return false;
        }
        if (idxDich == -1) {
            lyDo = "Tai khoan thu huong khong ton tai!";
            return false;
        }

        TaiKhoan* nguon = danhSachTaiKhoan[idxNguon].get();
        TaiKhoan* dich = danhSachTaiKhoan[idxDich].get();

        if (nguon->getTrangThai() != TrangThaiTaiKhoan::ACTIVE) {
            lyDo = "Tai khoan chuyen tien khong o trang thai hoat dong!";
            return false;
        }
        if (dich->getTrangThai() != TrangThaiTaiKhoan::ACTIVE) {
            lyDo = "Tai khoan nhan tien dang bi khoa hoac da dong!";
            return false;
        }

        if (!laSoHuuHan(soTien) || soTien <= 0) {
            lyDo = "So tien chuyen phai la so thuc duong hop le!";
            return false;
        }
        if (soTien < 10000.0) {
            lyDo = "So tien chuyen toi thieu la 10,000 VND!";
            return false;
        }

        // Xac thuc PIN tai khoan nguon
        if (!nguon->XacThucPIN(pin, lyDo)) {
            return false; // Loi sai PIN da duoc gan
        }

        double phi = BankConstants::PHI_CHUYEN_TIEN_CO_DINH;
        double tongTru = soTien + phi;

        // Kiem tra nguon co du tien (so tien + phi) theo quy tac da hinh
        if (!nguon->CoTheRut(tongTru, lyDo)) {
            lyDo = "So du khong du de thanh toan (Tien chuyen: " +
                   formatMoney(soTien) + " + Phi: " +
                   formatMoney(phi) + ")!";
            return false;
        }

        // Kiem tra tran so du tai khoan dich
        if (dich->getSoDu() > numeric_limits<double>::max() - soTien) {
            lyDo = "Tai khoan dich khong the tiep nhan them so tien nay!";
            return false;
        }

        // CAP NHAT SO DU NGUYEN TU (ATOMIC UPDATE)
        double truocNguon = nguon->getSoDu();
        double truocDich = dich->getSoDu();

        nguon->setSoDu(truocNguon - tongTru);
        dich->setSoDu(truocDich + soTien);

        double sauNguon = nguon->getSoDu();
        double sauDich = dich->getSoDu();

        string maGD = taoMaGiaoDich();
        string tg = layThoiGianHienTai();

        // Ghi nhat ky tai khoan chuyen
        GiaoDich gdNguon(maGD, LoaiGiaoDich::CHUYEN_TIEN_DI, soTKNguon, soTKDich,
                         soTien, phi, tg, truocNguon, sauNguon, "THANH_CONG",
                         "Chuyen tien den TK " + soTKDich + " (" + dich->getTenChuTaiKhoan() + ")");
        nguon->ThemGiaoDich(gdNguon);

        // Ghi nhat ky tai khoan nhan
        GiaoDich gdDich(maGD, LoaiGiaoDich::CHUYEN_TIEN_DEN, soTKNguon, soTKDich,
                        soTien, 0.0, tg, truocDich, sauDich, "THANH_CONG",
                        "Nhan tien tu TK " + soTKNguon + " (" + nguon->getTenChuTaiKhoan() + ")");
        dich->ThemGiaoDich(gdDich);

        lyDo = "Chuyen tien thanh cong den TK " + soTKDich + " (" + dich->getTenChuTaiKhoan() + ")!";
        if (sauNguon < nguon->getNguongCanhBao()) {
            lyDo += "\n[CANH BAO]: So du TK nguon (" + formatMoney(sauNguon) +
                    ") da xuong duoi nguong canh bao (" +
                    formatMoney(nguon->getNguongCanhBao()) + ")!";
        }
        return true;
    }

    // ==================== TRA CUU VA THONG KE ====================

    void HienThiTatCaTaiKhoan() const {
        if (danhSachTaiKhoan.empty()) {
            cout << UI::yellow() << "He thong hien chua co tai khoan nao.\n" << UI::reset();
            return;
        }

        cout << "\n" << UI::blue() << string(96, '=') << UI::reset() << "\n";
        cout << UI::bold() << "                     DANH SACH TAI KHOAN HE THONG (LAUDAITINHAI BANK)" << UI::reset() << "\n";
        cout << UI::blue() << string(96, '=') << UI::reset() << "\n";
        cout << UI::cyan()
             << left << setw(5)  << "STT"
             << setw(16) << "SO TAI KHOAN"
             << setw(26) << "CHU TAI KHOAN"
             << setw(16) << "LOAI TK"
             << setw(14) << "TRANG THAI"
             << right << setw(19) << "SO DU THUC TE"
             << UI::reset() << "\n";
        cout << string(96, '-') << "\n";

        for (size_t i = 0; i < danhSachTaiKhoan.size(); ++i) {
            const auto& tk = danhSachTaiKhoan[i];
            cout << left << setw(5)  << (i + 1)
                 << setw(16) << tk->getSoTaiKhoan()
                 << setw(26) << tk->getTenChuTaiKhoan()
                 << setw(16) << tk->getLoaiTaiKhoan()
                 << setw(14) << tk->getTrangThaiString()
                 << right << setw(19) << formatMoney(tk->getSoDuCongKhai()) << "\n";
        }
        cout << UI::blue() << string(96, '=') << UI::reset() << "\n";
    }

    // Tim kiem tai khoan theo so tai khoan hoac ten chu tai khoan (khong phan biet hoa thuong)
    void TimKiemTaiKhoan(const string& tuKhoa) const {
        if (tuKhoa.empty()) {
            cout << "Tu khoa tim kiem khong duoc de trong!\n";
            return;
        }

        string kwLower = tuKhoa;
        transform(kwLower.begin(), kwLower.end(), kwLower.begin(), ::tolower);

        bool timThay = false;
        for (const auto& tk : danhSachTaiKhoan) {
            string soTKLower = tk->getSoTaiKhoan();
            transform(soTKLower.begin(), soTKLower.end(), soTKLower.begin(), ::tolower);

            string tenLower = tk->getTenChuTaiKhoan();
            transform(tenLower.begin(), tenLower.end(), tenLower.begin(), ::tolower);

            if (soTKLower.find(kwLower) != string::npos || tenLower.find(kwLower) != string::npos) {
                cout << "\n--------------------------------------------------\n";
                tk->HienThiThongTin();
                timThay = true;
            }
        }

        if (!timThay) {
            cout << "Khong tim thay tai khoan nao phu hop voi tu khoa \"" << tuKhoa << "\"!\n";
        }
    }

    // Tim tai khoan co so du lon nhat trong he thong
    void TimTaiKhoanSoDuLonNhat() const {
        if (danhSachTaiKhoan.empty()) {
            cout << "Ngan hang chua co tai khoan nao!\n";
            return;
        }

        auto itMax = max_element(danhSachTaiKhoan.begin(), danhSachTaiKhoan.end(),
            [](const unique_ptr<TaiKhoan>& a, const unique_ptr<TaiKhoan>& b) {
                return a->getSoDuCongKhai() < b->getSoDuCongKhai();
            });

        cout << "\n=== TAI KHOAN CO SO DU LON NHAT HE THONG ===\n";
        (*itMax)->HienThiThongTin();
    }

    // Tinh va cong lai cho tat ca cac tai khoan tiet kiem
    void TinhVaCongLaiTietKiem() {
        int dem = 0;
        double tongLai = 0.0;

        for (auto& tk : danhSachTaiKhoan) {
            if (tk->getLoaiTaiKhoan() == "Tiet kiem" && tk->getTrangThai() == TrangThaiTaiKhoan::ACTIVE) {
                auto tkTK = dynamic_cast<TaiKhoanTietKiem*>(tk.get());
                if (tkTK) {
                    GiaoDich gd;
                    if (tkTK->CongLaiTietKiem(gd)) {
                        dem++;
                        tongLai += gd.getSoTien();
                        cout << "-> Da cong " << formatMoney(gd.getSoTien())
                             << " vao TK " << tkTK->getSoTaiKhoan() << " (" << tkTK->getTenChuTaiKhoan() << ")\n";
                    }
                }
            }
        }

        cout << "\nKet toan hoan tat: Da cong lai cho " << dem
             << " tai khoan voi tong so tien: " << formatMoney(tongLai) << ".\n";
    }

    // Bao cao thong ke toan ngan hang
    void BaoCaoThongKe() const {
        double tongSoDu = 0.0;
        double tongNap = 0.0;
        double tongRut = 0.0;
        double tongChuyen = 0.0;
        int soTKHoatDong = 0;
        int soTKBiKhoa = 0;
        int soTKDaDong = 0;

        for (const auto& tk : danhSachTaiKhoan) {
            tongSoDu += tk->getSoDuCongKhai();
            if (tk->getTrangThai() == TrangThaiTaiKhoan::ACTIVE) soTKHoatDong++;
            else if (tk->getTrangThai() == TrangThaiTaiKhoan::LOCKED) soTKBiKhoa++;
            else if (tk->getTrangThai() == TrangThaiTaiKhoan::CLOSED) soTKDaDong++;

            for (const auto& gd : tk->getLichSuGiaoDich()) {
                if (gd.getLoai() == LoaiGiaoDich::NAP_TIEN) {
                    tongNap += gd.getSoTien();
                } else if (gd.getLoai() == LoaiGiaoDich::RUT_TIEN) {
                    tongRut += gd.getSoTien();
                } else if (gd.getLoai() == LoaiGiaoDich::CHUYEN_TIEN_DI) {
                    tongChuyen += gd.getSoTien();
                }
            }
        }

        cout << "\n" << UI::blue() << string(72, '=') << UI::reset() << "\n";
        cout << UI::bold() << "               BAO CAO THONG KE HE THONG LAUDAITINHAI BANK" << UI::reset() << "\n";
        cout << UI::blue() << string(72, '=') << UI::reset() << "\n";
        cout << "  Tong so tai khoan:              " << UI::bold() << danhSachTaiKhoan.size() << UI::reset() << "\n";
        cout << "   - So tai khoan dang hoat dong: " << UI::green() << soTKHoatDong << UI::reset() << "\n";
        cout << "   - So tai khoan dang bi khoa:   " << UI::red() << soTKBiKhoa << UI::reset() << "\n";
        cout << "   - So tai khoan da dong:        " << UI::dim() << soTKDaDong << UI::reset() << "\n";
        cout << "  Tong so du tien gui khach hang: " << UI::cyan() << formatMoney(tongSoDu) << UI::reset() << "\n";
        cout << "  Tong tien da nap vao he thong:  " << formatMoney(tongNap) << "\n";
        cout << "  Tong tien da rut khoi he thong: " << formatMoney(tongRut) << "\n";
        cout << "  Tong luong tien giao dich chuyen:" << formatMoney(tongChuyen) << "\n";
        cout << UI::blue() << string(72, '=') << UI::reset() << "\n";
    }

    // Tra cuu giao dich theo ma tren pham vi toan he thong
    void TraCuuGiaoDichToanHeThong(const string& maGD) const {
        bool timThay = false;
        for (const auto& tk : danhSachTaiKhoan) {
            GiaoDich gd;
            if (tk->TimGiaoDichTheoMa(maGD, gd)) {
                cout << "\nTim thay giao dich thuoc tai khoan: " << tk->getSoTaiKhoan()
                     << " (" << tk->getTenChuTaiKhoan() << ")\n";
                cout << gd;
                timThay = true;
            }
        }
        if (!timThay) {
            cout << "Khong tim thay giao dich voi ma \"" << maGD << "\" tren toan he thong!\n";
        }
    }

    // ==================== LUU VA PHUC HOI DU LIEU (FILE PERSISTENCE) ====================
    /**
     * Luu du lieu vao file:
     * Dinh dang luu:
     * ACCOUNT|[Loai]|[SoTK]|[Ten]|[SoDu]|[ThuocTinhRieng]|[Salt]|[MKHash]|[PINHash]|[TrangThai]|[SaiMK]|[SaiPIN]|[Nguong]|[RutNgay]|[NgayGD]
     * TX|[SoTK]|[MaGD]|[Loai]|[Nguon]|[Dich]|[SoTien]|[Phi]|[ThoiGian]|[Truoc]|[Sau]|[TrangThai]|[NoiDung]
     */
    bool LuuDuLieu(const string& tenFile = BankConstants::FILE_DU_LIEU_MAC_DINH) const {
        ofstream out(tenFile);
        if (!out.is_open()) return false;

        out << "# NGAN HANG DU LIEU AN TOAN - PHIEN BAN 2.0\n";
        for (const auto& tk : danhSachTaiKhoan) {
            string loai = tk->getLoaiTaiKhoan();
            double thuocTinhRieng = 0.0;
            if (loai == "Tiet kiem") {
                const auto* tkTK = dynamic_cast<const TaiKhoanTietKiem*>(tk.get());
                if (tkTK) thuocTinhRieng = tkTK->getLaiSuat();
            } else {
                const auto* tkTT = dynamic_cast<const TaiKhoanThanhToan*>(tk.get());
                if (tkTT) thuocTinhRieng = tkTT->getHanMucTinDung();
            }

            out << "ACCOUNT|"
                << loai << "|"
                << tk->getSoTaiKhoan() << "|"
                << tk->getTenChuTaiKhoan() << "|"
                << fixed << setprecision(2) << tk->getSoDuCongKhai() << "|"
                << thuocTinhRieng << "|"
                << tk->getSalt() << "|"
                << tk->getMatKhauHash() << "|"
                << tk->getPinHash() << "|"
                << static_cast<int>(tk->getTrangThai()) << "|"
                << tk->getSoLanDangNhapSai() << "|"
                << tk->getSoLanNhapPinSai() << "|"
                << tk->getNguongCanhBao() << "|"
                << tk->tongRutTrongNgay << "|"
                << tk->ngayGiaoDichHienTai << "\n";

            for (const auto& gd : tk->getLichSuGiaoDich()) {
                out << "TX|"
                    << tk->getSoTaiKhoan() << "|"
                    << gd.getMaGiaoDich() << "|"
                    << static_cast<int>(gd.getLoai()) << "|"
                    << gd.getSoTaiKhoanNguon() << "|"
                    << gd.getSoTaiKhoanDich() << "|"
                    << fixed << setprecision(2) << gd.getSoTien() << "|"
                    << gd.getPhiGiaoDich() << "|"
                    << gd.getThoiGian() << "|"
                    << gd.getSoDuTruoc() << "|"
                    << gd.getSoDuSau() << "|"
                    << gd.getTrangThai() << "|"
                    << gd.getNoiDung() << "\n";
            }
        }
        out.close();
        return true;
    }

    // Doc va phuc hoi toan bo tai khoan va nhat ky giao dich tu file
    bool TaiDuLieu(const string& tenFile = BankConstants::FILE_DU_LIEU_MAC_DINH) {
        ifstream in(tenFile);
        if (!in.is_open()) return false;

        danhSachTaiKhoan.clear();
        string dong;
        while (getline(in, dong)) {
            if (dong.empty() || dong[0] == '#') continue;

            stringstream ss(dong);
            string tag;
            getline(ss, tag, '|');

            if (tag == "ACCOUNT") {
                string loai, soTK, ten, salt, mkHash, pinHash, ngayGD;
                string sSoDu, sThuocTinh, sTT, sSaiMK, sSaiPIN, sNguong, sRutNgay;

                getline(ss, loai, '|');
                getline(ss, soTK, '|');
                getline(ss, ten, '|');
                getline(ss, sSoDu, '|');
                getline(ss, sThuocTinh, '|');
                getline(ss, salt, '|');
                getline(ss, mkHash, '|');
                getline(ss, pinHash, '|');
                getline(ss, sTT, '|');
                getline(ss, sSaiMK, '|');
                getline(ss, sSaiPIN, '|');
                getline(ss, sNguong, '|');
                getline(ss, sRutNgay, '|');
                getline(ss, ngayGD, '|');

                double soDu = stod(sSoDu);
                double thuocTinh = stod(sThuocTinh);
                TrangThaiTaiKhoan tt = static_cast<TrangThaiTaiKhoan>(stoi(sTT));
                int saiMK = stoi(sSaiMK);
                int saiPIN = stoi(sSaiPIN);
                double nguong = stod(sNguong);
                double rutNgay = stod(sRutNgay);    

                unique_ptr<TaiKhoan> tk;
                if (loai == "Tiet kiem") {
                    tk = make_unique<TaiKhoanTietKiem>(soTK, ten, soDu, thuocTinh);
                } else {
                    tk = make_unique<TaiKhoanThanhToan>(soTK, ten, soDu, thuocTinh);
                }

                tk->NapThongTinBaoMatTuFile(salt, mkHash, pinHash, tt, saiMK, saiPIN, nguong, rutNgay, ngayGD);
                danhSachTaiKhoan.push_back(move(tk));
            } else if (tag == "TX") {
                string soTK, maGD, sLoai, nguon, dich, sTien, sPhi, tg, sTruoc, sSau, tt, nd;
                getline(ss, soTK, '|');
                getline(ss, maGD, '|');
                getline(ss, sLoai, '|');
                getline(ss, nguon, '|');
                getline(ss, dich, '|');
                getline(ss, sTien, '|');
                getline(ss, sPhi, '|');
                getline(ss, tg, '|');
                getline(ss, sTruoc, '|');
                getline(ss, sSau, '|');
                getline(ss, tt, '|');
                getline(ss, nd, '|');

                int idx = TimTaiKhoanTheoSoTK(soTK);
                if (idx != -1) {
                    GiaoDich gd(maGD, static_cast<LoaiGiaoDich>(stoi(sLoai)), nguon, dich,
                               stod(sTien), stod(sPhi), tg, stod(sTruoc), stod(sSau), tt, nd);
                    danhSachTaiKhoan[idx]->ThemGiaoDich(gd);
                }
            }
        }
        in.close();
        return true;
    }
};

// ============================================================================
// CAC TIEN ICH GIAO DIEN CONSOLE VA NHAP LIEU AN TOAN
// ============================================================================

int nhapLuaChonSo() {
    int luaChon;
    if (!(cin >> luaChon)) {
        if (cin.eof()) return 0;
        cin.clear();
        cin.ignore(numeric_limits<streamsize>::max(), '\n');
        return -1;
    }
    cin.ignore(numeric_limits<streamsize>::max(), '\n');
    return luaChon;
}

double nhapSoTien(const string& nhan, bool choPhep0 = false) {
    while (true) {
        cout << nhan;
        string s;
        if (!(cin >> s)) {
            if (cin.eof()) return -1;
            cin.clear();
            cin.ignore(numeric_limits<streamsize>::max(), '\n');
            continue;
        }
        cin.ignore(numeric_limits<streamsize>::max(), '\n');

        string cleanStr = "";
        for (char c : s) {
            if (c != ',') cleanStr += c;
        }

        try {
            size_t idx = 0;
            double soTien = stod(cleanStr, &idx);
            if (idx == cleanStr.length() && laSoHuuHan(soTien)) {
                if (choPhep0 && soTien == 0.0) {
                    return 0.0;
                }
                if (soTien > 0) {
                    return soTien;
                }
            }
        } catch (...) {}

        cout << UI::red() << "[Loi]: So tien nhap khong hop le! Vui long nhap so thuc duong huu han"
             << (choPhep0 ? " (hoac 0 de huy)" : "") << ".\n" << UI::reset();
    }
}

string nhapChuoiKhongRong(const string& nhan) {
    string s;
    while (true) {
        cout << nhan;
        if (!getline(cin, s)) return "";
        if (!s.empty()) return s;
        cout << UI::red() << "[Loi]: Du lieu khong duoc de trong! Vui long nhap lai.\n" << UI::reset();
    }
}

string nhapMaPIN(const string& nhan) {
    return NhapMatKhauAnToan(nhan, BankConstants::DO_DAI_PIN_YEU_CAU, true, BankConstants::DO_DAI_PIN_YEU_CAU);
}

// ============================================================================
// MENU CONSOLE VA DIEU HUONG
// ============================================================================

void menuLichSuGiaoDich(TaiKhoan* tk) {
    int chon;
    do {
        clearScreen();
        printBanner("TRA CUU LICH SU GIAO DICH", "So tai khoan: " + tk->getSoTaiKhoan());
        cout << "  " << UI::cyan() << "[1]" << UI::reset() << " Xem toan bo lich su (moi nhat truoc)\n";
        cout << "  " << UI::cyan() << "[2]" << UI::reset() << " Xem giao dich gan nhat\n";
        cout << "  " << UI::cyan() << "[3]" << UI::reset() << " Tim kiem theo ma giao dich\n";
        cout << "  " << UI::cyan() << "[4]" << UI::reset() << " Loc giao dich nap tien\n";
        cout << "  " << UI::cyan() << "[5]" << UI::reset() << " Loc giao dich rut tien\n";
        cout << "  " << UI::cyan() << "[6]" << UI::reset() << " Loc giao dich chuyen tien di / den\n";
        cout << "  " << UI::red()  << "[0]" << UI::reset() << " Quay lai menu tai khoan\n";
        printDivider(72);
        cout << UI::bold() << "Lua chon: " << UI::reset();
        chon = nhapLuaChonSo();

        switch (chon) {
            case 1:
                tk->HienThiLichSu();
                pauseScreen();
                break;
            case 2:
                tk->HienThiGiaoDichGanNhat();
                pauseScreen();
                break;
            case 3: {
                string maGD = nhapChuoiKhongRong("Nhap ma giao dich can tra cuu (hoac 0 de huy): ");
                if (maGD == "0") {
                    showWarning("Da huy tra cuu giao dich.");
                } else {
                    GiaoDich gd;
                    if (tk->TimGiaoDichTheoMa(maGD, gd)) {
                        cout << gd;
                    } else {
                        showError("Khong tim thay giao dich voi ma: " + maGD);
                    }
                }
                pauseScreen();
                break;
            }
            case 4:
                tk->LocGiaoDichTheoLoai(LoaiGiaoDich::NAP_TIEN);
                pauseScreen();
                break;
            case 5:
                tk->LocGiaoDichTheoLoai(LoaiGiaoDich::RUT_TIEN);
                pauseScreen();
                break;
            case 6:
                tk->LocGiaoDichTheoLoai(LoaiGiaoDich::CHUYEN_TIEN_DI);
                tk->LocGiaoDichTheoLoai(LoaiGiaoDich::CHUYEN_TIEN_DEN);
                pauseScreen();
                break;
            case 0:
                break;
            default:
                showError("Lua chon khong hop le!");
                pauseScreen();
        }
    } while (chon != 0);
}

// Menu danh cho khach hang da dang nhap thanh cong
void menuKhachHang(TaiKhoan* tk, NganHang& bank) {
    int chon;
    do {
        clearScreen();
        printBanner("TRANG CHU KHACH HANG");
        cout << "  " << UI::bold() << "SO TK: " << UI::cyan() << tk->getSoTaiKhoan() << UI::reset()
             << " | " << UI::bold() << "CHU TK: " << UI::white() << tk->getTenChuTaiKhoan() << UI::reset()
             << " | " << UI::bold() << "LOAI: " << UI::yellow() << tk->getLoaiTaiKhoan() << UI::reset() << "\n";
        cout << "  " << UI::bold() << "SO DU KHA DUNG: " << UI::green() << formatMoney(tk->getSoDuKhaDung()) << UI::reset() << "\n";
        printDivider(72);
        cout << "  " << UI::cyan() << "[1]" << UI::reset() << " Xem thong tin tai khoan & So du kha dung\n";
        cout << "  " << UI::cyan() << "[2]" << UI::reset() << " Nap tien vao tai khoan (Yeu cau PIN)\n";
        cout << "  " << UI::cyan() << "[3]" << UI::reset() << " Rut tien tu tai khoan (Yeu cau PIN)\n";
        cout << "  " << UI::cyan() << "[4]" << UI::reset() << " Chuyen tien den tai khoan khac (Yeu cau PIN)\n";
        cout << "  " << UI::cyan() << "[5]" << UI::reset() << " Tra cuu lich su giao dich\n";
        cout << "  " << UI::cyan() << "[6]" << UI::reset() << " Doi mat khau dang nhap\n";
        cout << "  " << UI::cyan() << "[7]" << UI::reset() << " Doi ma PIN giao dich\n";
        cout << "  " << UI::cyan() << "[8]" << UI::reset() << " Xuat sao ke ra file (TXT / CSV)\n";
        cout << "  " << UI::cyan() << "[9]" << UI::reset() << " Cai dat nguong canh bao so du toi thieu\n";
        cout << "  " << UI::red()  << "[0]" << UI::reset() << " Dang xuat tai khoan\n";
        printDivider(72);
        cout << UI::bold() << "Lua chon cua ban: " << UI::reset();
        chon = nhapLuaChonSo();

        switch (chon) {
            case 1:
                clearScreen();
                printBanner("THONG TIN TAI KHOAN CHI TIET");
                tk->HienThiThongTin();
                pauseScreen();
                break;

            case 2: {
                clearScreen();
                printBanner("NAP TIEN VAO TAI KHOAN");
                cout << "  So du hien tai: " << UI::green() << formatMoney(tk->getSoDuCongKhai()) << UI::reset() << "\n\n";
                double soTien = nhapSoTien("Nhap so tien can nap (VND) [Nhap 0 de huy]: ", true);
                if (soTien == 0.0) {
                    showWarning("Da huy thao tac nap tien.");
                    pauseScreen();
                    break;
                }
                string pin = nhapMaPIN("Nhap ma PIN giao dich (Enter de huy): ");
                if (pin.empty()) {
                    showWarning("Da huy thao tac do khong nhap PIN.");
                    pauseScreen();
                    break;
                }
                string lyDo;
                if (tk->ThucHienNapTien(soTien, pin, lyDo)) {
                    showSuccess(lyDo);
                    cout << "So du moi: " << UI::green() << formatMoney(tk->getSoDuCongKhai()) << UI::reset() << "\n";
                } else {
                    showError(lyDo);
                }
                pauseScreen();
                break;
            }

            case 3: {
                clearScreen();
                printBanner("RUT TIEN MAT");
                cout << "  So du kha dung: " << UI::green() << formatMoney(tk->getSoDuKhaDung()) << UI::reset() << "\n\n";
                double soTien = nhapSoTien("Nhap so tien can rut (VND) [Nhap 0 de huy]: ", true);
                if (soTien == 0.0) {
                    showWarning("Da huy thao tac rut tien.");
                    pauseScreen();
                    break;
                }
                string pin = nhapMaPIN("Nhap ma PIN giao dich (Enter de huy): ");
                if (pin.empty()) {
                    showWarning("Da huy thao tac do khong nhap PIN.");
                    pauseScreen();
                    break;
                }
                string lyDo;
                if (tk->ThucHienRutTien(soTien, pin, lyDo)) {
                    showSuccess(lyDo);
                    cout << "So du con lai: " << UI::green() << formatMoney(tk->getSoDuCongKhai()) << UI::reset() << "\n";
                } else {
                    showError(lyDo);
                }
                pauseScreen();
                break;
            }

            case 4: {
                clearScreen();
                printBanner("CHUYEN TIEN NOI BO NGAN HANG");
                cout << "  So du kha dung: " << UI::green() << formatMoney(tk->getSoDuKhaDung()) << UI::reset() << "\n";
                cout << "  Phi chuyen tien: " << formatMoney(BankConstants::PHI_CHUYEN_TIEN_CO_DINH) << "\n\n";
                string tkDich = nhapChuoiKhongRong("Nhap so tai khoan thu huong (Nhap 0 de huy): ");
                if (tkDich == "0") {
                    showWarning("Da huy giao dich chuyen tien.");
                    pauseScreen();
                    break;
                }
                double soTien = nhapSoTien("Nhap so tien muon chuyen (VND) [Nhap 0 de huy]: ", true);
                if (soTien == 0.0) {
                    showWarning("Da huy giao dich chuyen tien.");
                    pauseScreen();
                    break;
                }
                string pin = nhapMaPIN("Nhap ma PIN de xac thuc chuyen tien (Enter de huy): ");
                if (pin.empty()) {
                    showWarning("Da huy giao dich do khong nhap PIN.");
                    pauseScreen();
                    break;
                }
                string lyDo;
                if (bank.ChuyenTien(tk->getSoTaiKhoan(), tkDich, soTien, pin, lyDo)) {
                    showSuccess(lyDo);
                    cout << "So du hien tai: " << UI::green() << formatMoney(tk->getSoDuCongKhai()) << UI::reset() << "\n";
                } else {
                    showError(lyDo);
                }
                pauseScreen();
                break;
            }

            case 5:
                menuLichSuGiaoDich(tk);
                break;

            case 6: {
                clearScreen();
                printBanner("DOI MAT KHAU DANG NHAP");
                string mkCu = NhapMatKhauAnToan("Nhap mat khau hien tai (Enter de huy): ", 32);
                if (mkCu.empty()) {
                    showWarning("Da huy doi mat khau.");
                    pauseScreen();
                    break;
                }
                string mkMoi = NhapMatKhauAnToan("Nhap mat khau moi: ", 32);
                if (mkMoi.empty()) {
                    showWarning("Da huy doi mat khau.");
                    pauseScreen();
                    break;
                }
                string xnMK = NhapMatKhauAnToan("Xac nhan mat khau moi: ", 32);
                string tb;
                if (tk->DoiMatKhau(mkCu, mkMoi, xnMK, tb)) {
                    showSuccess(tb);
                } else {
                    showError(tb);
                }
                pauseScreen();
                break;
            }

            case 7: {
                clearScreen();
                printBanner("DOI MA PIN GIAO DICH");
                string pinCu = nhapMaPIN("Nhap ma PIN hien tai (Enter de huy): ");
                if (pinCu.empty()) {
                    showWarning("Da huy doi ma PIN.");
                    pauseScreen();
                    break;
                }
                string pinMoi = nhapMaPIN("Nhap ma PIN moi (6 chu so): ");
                if (pinMoi.empty()) {
                    showWarning("Da huy doi ma PIN.");
                    pauseScreen();
                    break;
                }
                string xnPin = nhapMaPIN("Xac nhan ma PIN moi: ");
                string tb;
                if (tk->DoiPIN(pinCu, pinMoi, xnPin, tb)) {
                    showSuccess(tb);
                } else {
                    showError(tb);
                }
                pauseScreen();
                break;
            }

            case 8: {
                clearScreen();
                printBanner("XUAT SAO KE RA TAP TIN");
                cout << "  " << UI::cyan() << "[1]" << UI::reset() << " File van ban chi tiet (TXT)\n";
                cout << "  " << UI::cyan() << "[2]" << UI::reset() << " File bang tinh (CSV)\n";
                cout << "  " << UI::red()  << "[0]" << UI::reset() << " Huy bo\n";
                printDivider(72);
                cout << "Chon: ";
                int fChon = nhapLuaChonSo();
                if (fChon == 0) {
                    showWarning("Da huy thao tac xuat sao ke.");
                    pauseScreen();
                    break;
                }
                string tenFileDefault = "SaoKe_" + tk->getSoTaiKhoan() + (fChon == 2 ? ".csv" : ".txt");
                cout << "Nhap ten file (mac dinh: " << tenFileDefault << "): ";
                string tenFile;
                getline(cin, tenFile);
                if (tenFile.empty()) tenFile = tenFileDefault;

                if (tk->XuatSaoKe(tenFile, fChon == 2)) {
                    showSuccess("Da xuat sao ke tai khoan ra file \"" + tenFile + "\"!");
                } else {
                    showError("Khong the ghi file \"" + tenFile + "\"!");
                }
                pauseScreen();
                break;
            }

            case 9: {
                clearScreen();
                printBanner("CAI DAT NGUONG CANH BAO SO DU");
                cout << "  Nguong canh bao so du hien tai: " << formatMoney(tk->getNguongCanhBao()) << "\n";
                double nguongMoi = nhapSoTien("Nhap nguong canh bao so du moi (VND) [Nhap 0 de huy]: ", true);
                if (nguongMoi == 0.0) {
                    showWarning("Da huy thay doi nguong canh bao.");
                } else {
                    tk->setNguongCanhBao(nguongMoi);
                    showSuccess("Da cap nhat nguong canh bao moi: " + formatMoney(nguongMoi));
                }
                pauseScreen();
                break;
            }

            case 0:
                showInfo("Dang dang xuat khoi tai khoan...");
                break;

            default:
                showError("Lua chon khong hop le!");
                pauseScreen();
        }
    } while (chon != 0);
}

// Menu danh cho Quan tri vien he thong (Admin)
void menuQuanTri(NganHang& bank) {
    int chon;
    do {
        clearScreen();
        printBanner("MENU QUAN TRI VIEN (ADMIN)", "Quyen han cap cao");
        cout << "  " << UI::cyan() << "[1]" << UI::reset() << " Hien thi danh sach tat ca tai khoan\n";
        cout << "  " << UI::cyan() << "[2]" << UI::reset() << " Tim kiem tai khoan (theo So TK hoac Ten chu TK)\n";
        cout << "  " << UI::cyan() << "[3]" << UI::reset() << " Tim tai khoan co so du lon nhat he thong\n";
        cout << "  " << UI::cyan() << "[4]" << UI::reset() << " Khoa / Mo khoa / Dong tai khoan khach hang\n";
        cout << "  " << UI::cyan() << "[5]" << UI::reset() << " Tinh va ket toan lai tiet kiem hang thang\n";
        cout << "  " << UI::cyan() << "[6]" << UI::reset() << " Bao cao thong ke toan ngan hang\n";
        cout << "  " << UI::cyan() << "[7]" << UI::reset() << " Tra cuu giao dich theo ma toan he thong\n";
        cout << "  " << UI::cyan() << "[8]" << UI::reset() << " Luu du lieu toan he thong ra file\n";
        cout << "  " << UI::cyan() << "[9]" << UI::reset() << " Tai lai du lieu he thong tu file\n";
        cout << "  " << UI::red()  << "[0]" << UI::reset() << " Dang xuat quan tri vien\n";
        printDivider(72);
        cout << UI::bold() << "Lua chon: " << UI::reset();
        chon = nhapLuaChonSo();

        switch (chon) {
            case 1:
                clearScreen();
                bank.HienThiTatCaTaiKhoan();
                pauseScreen();
                break;

            case 2: {
                clearScreen();
                printBanner("TIM KIEM TAI KHOAN");
                string tuKhoa = nhapChuoiKhongRong("Nhap so TK hoac ten chu tai khoan (0 de huy): ");
                if (tuKhoa == "0") {
                    showWarning("Da huy tim kiem.");
                } else {
                    bank.TimKiemTaiKhoan(tuKhoa);
                }
                pauseScreen();
                break;
            }

            case 3:
                clearScreen();
                printBanner("TAI KHOAN CO SO DU LON NHAT");
                bank.TimTaiKhoanSoDuLonNhat();
                pauseScreen();
                break;

            case 4: {
                clearScreen();
                printBanner("QUAN LY TRANG THAI TAI KHOAN");
                string soTK = nhapChuoiKhongRong("Nhap so tai khoan can thao tac (0 de huy): ");
                if (soTK == "0") {
                    showWarning("Da huy thao tac.");
                    pauseScreen();
                    break;
                }
                TaiKhoan* tk = bank.getTaiKhoanPtr(soTK);
                if (!tk) {
                    showError("Khong tim thay tai khoan voi so TK: " + soTK);
                    pauseScreen();
                    break;
                }

                cout << "  Trang thai hien tai: " << UI::yellow() << tk->getTrangThaiString() << UI::reset() << "\n\n";
                cout << "  " << UI::cyan() << "[1]" << UI::reset() << " Mo khoa tai khoan (ACTIVE) & reset so lan sai MK/PIN\n";
                cout << "  " << UI::cyan() << "[2]" << UI::reset() << " Khoa tai khoan (LOCKED)\n";
                cout << "  " << UI::cyan() << "[3]" << UI::reset() << " Dong tai khoan (CLOSED)\n";
                cout << "  " << UI::red()  << "[0]" << UI::reset() << " Huy bo\n";
                printDivider(72);
                cout << "Chon: ";
                int act = nhapLuaChonSo();

                if (act == 1) {
                    tk->MoKhoa();
                    showSuccess("Tai khoan " + soTK + " da duoc MO KHOA thanh cong!");
                } else if (act == 2) {
                    tk->KhoaTaiKhoan();
                    showSuccess("Tai khoan " + soTK + " da bi KHOA!");
                } else if (act == 3) {
                    tk->DongTaiKhoan();
                    showSuccess("Tai khoan " + soTK + " da bi DONG!");
                } else {
                    showWarning("Da huy thao tac.");
                }
                pauseScreen();
                break;
            }

            case 5:
                clearScreen();
                printBanner("TINH VA KET TOAN LAI TIET KIEM");
                bank.TinhVaCongLaiTietKiem();
                pauseScreen();
                break;

            case 6:
                clearScreen();
                bank.BaoCaoThongKe();
                pauseScreen();
                break;

            case 7: {
                clearScreen();
                printBanner("TRA CUU GIAO DICH TOAN HE THONG");
                string maGD = nhapChuoiKhongRong("Nhap ma giao dich can tra cuu (0 de huy): ");
                if (maGD == "0") {
                    showWarning("Da huy tra cuu.");
                } else {
                    bank.TraCuuGiaoDichToanHeThong(maGD);
                }
                pauseScreen();
                break;
            }

            case 8: {
                clearScreen();
                printBanner("LUU DU LIEU TOAN HE THONG");
                cout << "Nhap ten file luu du lieu (mac dinh: " << BankConstants::FILE_DU_LIEU_MAC_DINH << "): ";
                string fn;
                getline(cin, fn);
                if (fn.empty()) fn = BankConstants::FILE_DU_LIEU_MAC_DINH;
                if (bank.LuuDuLieu(fn)) {
                    showSuccess("Da luu toan bo du lieu ra file \"" + fn + "\"!");
                } else {
                    showError("Khong the luu du lieu vao file \"" + fn + "\"!");
                }
                pauseScreen();
                break;
            }

            case 9: {
                clearScreen();
                printBanner("NAP LAI DU LIEU HE THONG");
                cout << "Nhap ten file nap du lieu (mac dinh: " << BankConstants::FILE_DU_LIEU_MAC_DINH << "): ";
                string fn;
                getline(cin, fn);
                if (fn.empty()) fn = BankConstants::FILE_DU_LIEU_MAC_DINH;
                if (bank.TaiDuLieu(fn)) {
                    showSuccess("Da tai du lieu tu file \"" + fn + "\" thanh cong!");
                } else {
                    showError("Khong the doc du lieu tu file \"" + fn + "\"!");
                }
                pauseScreen();
                break;
            }

            case 0:
                showInfo("Dang thoat quyen quan tri vien...");
                break;

            default:
                showError("Lua chon khong hop le!");
                pauseScreen();
        }
    } while (chon != 0);
}

// Menu chinh cua he thong
void hienThiMenuChinh() {
    printBanner("HE THONG NGAN HANG SO - MENU CHINH", "LAUDAITINHAI BANK - Uy tin & An toan");
    cout << "  " << UI::cyan() << "[1]" << UI::reset() << " Dang nhap tai khoan khach hang\n";
    cout << "  " << UI::cyan() << "[2]" << UI::reset() << " Dang ky mo tai khoan tiet kiem\n";
    cout << "  " << UI::cyan() << "[3]" << UI::reset() << " Dang ky mo tai khoan thanh toan\n";
    cout << "  " << UI::cyan() << "[4]" << UI::reset() << " Dang nhap quan tri vien (Admin)\n";
    cout << "  " << UI::cyan() << "[5]" << UI::reset() << " Huong dan su dung & Gioi han bao mat demo\n";
    cout << "  " << UI::red()  << "[0]" << UI::reset() << " Thoat chuong trinh\n";
    printDivider(72);
    cout << UI::bold() << "Lua chon cua ban: " << UI::reset();
}

void hienThiThongTinBaoMatDemo() {
    printBanner("CHINH SACH BAO MAT & HUONG DAN SU DUNG", "LAUDAITINHAI BANK Security Standards");
    cout << "  " << UI::bold() << "1. QUY TAC MAT KHAU & PIN:" << UI::reset() << "\n";
    cout << "     - Mat khau va PIN duoc quan ly doc lap, khong bao gio luu o dang ro.\n";
    cout << "     - Thuat toan bam: SHA-256 kem Per-Account Salt ngau nhien cho tung TK.\n";
    cout << "     - Ma PIN bat buoc gom dung 6 chu so (giu nguyen so 0 o dau, vi du: 012345).\n\n";
    cout << "  " << UI::bold() << "2. QUY TAC KHOA TAI KHOAN:" << UI::reset() << "\n";
    cout << "     - Nhap sai mat khau 5 lan -> Tai khoan bi KHOA dang nhap.\n";
    cout << "     - Nhap sai ma PIN 3 lan   -> Tai khoan bi KHOA giao dich.\n";
    cout << "     - Chi co Quan tri vien (Admin) moi co tham quyen mo khoa tai khoan.\n\n";
    cout << "  " << UI::bold() << "3. TAI KHOAN ADMIN DEMO:" << UI::reset() << "\n";
    cout << "     - Tai khoan: " << UI::cyan() << "admin" << UI::reset() << "\n";
    cout << "     - Mat khau : " << UI::cyan() << "admin123" << UI::reset() << "\n\n";
    cout << "  " << UI::bold() << "4. GIOI HAN BAO MAT MO HINH DEMO:" << UI::reset() << "\n";
    cout << "     - Chuong trinh bam mat khau/PIN bang SHA-256 hop chuan trong C++.\n";
    cout << "     - File luu tru du lieu ghi nhan cac ma bam SHA-256 salt an toan.\n";
    printDivider(72);
}

// ============================================================================
// HAM MAIN (DIEM KHOI DAU CHUONG TRINH)
// ============================================================================
int main() {
    UI::initConsole();
    NganHang bank;

    // Tu dong tai du lieu tu file neu ton tai
    if (bank.TaiDuLieu(BankConstants::FILE_DU_LIEU_MAC_DINH)) {
        cout << UI::cyan() << "[He thong]: Da tu dong nap du lieu tu \""
             << BankConstants::FILE_DU_LIEU_MAC_DINH << "\".\n" << UI::reset();
    }

    int luaChon;
    do {
        clearScreen();
        hienThiMenuChinh();
        luaChon = nhapLuaChonSo();

        try {
            switch (luaChon) {
                case 1: {
                    // Dang nhap tai khoan khach hang
                    clearScreen();
                    printBanner("DANG NHAP TAI KHOAN KHACH HANG");
                    string soTK = nhapChuoiKhongRong("Nhap so tai khoan (hoac 0 de quay lai): ");
                    if (soTK == "0" || soTK.empty()) {
                        cout << UI::yellow() << "[Thong bao]: Huy luot dang nhap do loi dau vao hoac ket thuc du lieu.\n" << UI::reset();
                        pauseScreen();
                        break;
                    }

                    const int MAX_LAN_THU = BankConstants::MAX_SAI_MAT_KHAU;
                    for (int lanThu = 1; lanThu <= MAX_LAN_THU; ++lanThu) {
                        string matKhau = NhapMatKhauAnToan("Nhap mat khau: ", 32);
                        if (matKhau.empty()) {
                            cout << UI::yellow() << "[Thong bao]: Huy luot dang nhap do loi dau vao hoac ket thuc du lieu.\n" << UI::reset();
                            pauseScreen();
                            break;
                        }

                        string thongBaoLoi;
                        TaiKhoan* tk = bank.DangNhap(soTK, matKhau, thongBaoLoi);
                        if (tk) {
                            cout << UI::green() << "[Dang nhap thanh cong] Xin chao, " << tk->getTenChuTaiKhoan() << "!\n" << UI::reset();
                            pauseScreen();
                            menuKhachHang(tk, bank);
                            break;
                        }

                        cout << UI::red() << "[Loi dang nhap]: " << thongBaoLoi << "\n" << UI::reset();

                        // Kiem tra neu tai khoan da bi khoa hoac bi khoa sau lan thu nay
                        TaiKhoan* tkCheck = bank.getTaiKhoanPtr(soTK);
                        if (tkCheck && (tkCheck->getTrangThai() == TrangThaiTaiKhoan::LOCKED ||
                                        tkCheck->getTrangThai() == TrangThaiTaiKhoan::CLOSED)) {
                            cout << UI::yellow() << "[Thong bao]: Ket thuc luot dang nhap. Tu dong quay ve menu chinh.\n" << UI::reset();
                            pauseScreen();
                            break;
                        }

                        if (lanThu == MAX_LAN_THU) {
                            cout << UI::yellow() << "[Thong bao]: Ban da vuot qua so lan thu cho phep (5 lan). Tu dong quay ve menu chinh.\n" << UI::reset();
                            pauseScreen();
                        } else {
                            cout << UI::cyan() << "[Thong bao]: Vui long nhap lai mat khau! (Con " << (MAX_LAN_THU - lanThu) << " lan thu)\n" << UI::reset();
                        }
                    }
                    break;
                }

                case 2:
                case 3: {
                    // Mo tai khoan moi
                    clearScreen();
                    printBanner(luaChon == 2 ? "DANG KY MO TAI KHOAN TIET KIEM" : "DANG KY MO TAI KHOAN THANH TOAN");

                    unique_ptr<TaiKhoan> tk;
                    if (luaChon == 2) {
                        tk = make_unique<TaiKhoanTietKiem>();
                    } else {
                        tk = make_unique<TaiKhoanThanhToan>();
                    }

                    // Nhap thong tin thong qua toan tu >> (nap chong toan tu nhap xuat)
                    cin >> *tk;

                    string lyDo;
                    if (bank.ThemTaiKhoan(move(tk), lyDo)) {
                        showSuccess(lyDo);
                    } else {
                        showError(lyDo);
                    }
                    pauseScreen();
                    break;
                }

                case 4: {
                    // Dang nhap Admin
                    clearScreen();
                    printBanner("DANG NHAP QUAN TRI VIEN (ADMIN)");
                    string user = nhapChuoiKhongRong("Ten dang nhap quan tri (hoac 0 de huy): ");
                    if (user == "0") {
                        showWarning("Da huy dang nhap quan tri.");
                        pauseScreen();
                        break;
                    }
                    string pass = NhapMatKhauAnToan("Mat khau quan tri: ", 32);

                    if (bank.XacThucAdmin(user, pass)) {
                        showSuccess("Dang nhap quyen Quan tri vien thanh cong!");
                        pauseScreen();
                        menuQuanTri(bank);
                    } else {
                        showError("Thong tin quan tri vien khong chinh xac!");
                        pauseScreen();
                    }
                    break;
                }

                case 5:
                    clearScreen();
                    hienThiThongTinBaoMatDemo();
                    pauseScreen();
                    break;

                case 0: {
                    clearScreen();
                    printBanner("KET THUC PHIEN LAM VIEC", "LAUDAITINHAI BANK");
                    cout << "Tu dong sao luu du lieu he thong truoc khi thoat...\n";
                    if (bank.LuuDuLieu(BankConstants::FILE_DU_LIEU_MAC_DINH)) {
                        showSuccess("Da luu du lieu an toan vao \"" + BankConstants::FILE_DU_LIEU_MAC_DINH + "\".");
                    }
                    cout << UI::bold() << UI::green() << "Cam on ban da su dung chuong trinh Quan ly Ngan hang!\n" << UI::reset();
                    break;
                }

                default:
                    showError("Lua chon khong hop le! Vui long chon cac chuc nang tu 0 den 5.");
                    pauseScreen();
            }
        } catch (const exception& e) {
            showError(string("Ngoai le bat duoc: ") + e.what());
            pauseScreen();
        }

    } while (luaChon != 0);

    return 0;
}

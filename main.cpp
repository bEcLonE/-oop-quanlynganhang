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

#ifdef _WIN32
#include <conio.h>
#include <io.h>
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
        cout << left << setw(22) << maGiaoDich
             << setw(20) << thoiGian
             << setw(22) << loaiGDToString(loai)
             << right << setw(15) << fixed << setprecision(2) << soTien << " VND"
             << setw(13) << fixed << setprecision(2) << phiGiaoDich << " VND"
             << setw(16) << fixed << setprecision(2) << soDuSau << " VND\n";
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
        out << "So tien:       " << fixed << setprecision(2) << gd.soTien << " VND\n"
            << "Phi giao dich: " << fixed << setprecision(2) << gd.phiGiaoDich << " VND\n"
            << "So du truoc:   " << fixed << setprecision(2) << gd.soDuTruoc << " VND\n"
            << "So du sau:     " << fixed << setprecision(2) << gd.soDuSau << " VND\n"
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

                // 4. Phim Ctrl+C
                if (ch == 3) {
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
#else
        // Fallback cho POSIX / Linux / macOS
        if (!isatty(fileno(stdin))) {
            if (!getline(cin, res)) return "";
            if (!res.empty() && res.back() == '\r') res.pop_back();
        } else {
            termios oldt, newt;
            tcgetattr(STDIN_FILENO, &oldt);
            newt = oldt;
            newt.c_lflag &= ~(ECHO);
            tcsetattr(STDIN_FILENO, TCSANOW, &newt);
            while (true) {
                char c = getchar();
                if (c == '\n' || c == '\r') {
                    cout << "\n";
                    break;
                }
                if (c == 127 || c == '\b') {
                    if (!res.empty()) {
                        res.pop_back();
                        cout << "\b \b" << flush;
                    }
                    continue;
                }
                if (c == 27) { // Escape sequence
                    getchar(); getchar();
                    continue;
                }
                if (chiChuSo && !isdigit(static_cast<unsigned char>(c))) continue;
                if (res.length() < maxLen) {
                    res.push_back(c);
                    cout << '*' << flush;
                }
            }
            tcsetattr(STDIN_FILENO, TCSANOW, &oldt);
        }
#endif

        // Kiem tra chuoi rong
        if (res.empty()) {
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
        if (!(in >> soDu)) {
            in.clear();
            in.ignore(numeric_limits<streamsize>::max(), '\n');
            throw invalid_argument("So du phai la mot con so hop le!");
        }
        in.ignore(numeric_limits<streamsize>::max(), '\n');

        if (!laSoHuuHan(soDu) || soDu < 0) {
            throw invalid_argument("So du ban dau phai >= 0 va la so thuc huu han!");
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
        out << "So tai khoan:       " << soTaiKhoan << '\n';
        out << "Chu tai khoan:      " << tenChuTaiKhoan << '\n';
        out << "Trang thai:         " << trangThaiToString(trangThai) << '\n';
        out << "So du thuc te:      " << fixed << setprecision(2) << soDu << " VND\n";
        out << "So du kha dung:     " << fixed << setprecision(2) << getSoDuKhaDung() << " VND\n";
        out << "Nguong canh bao:    " << fixed << setprecision(2) << nguongCanhBaoSoDu << " VND\n";
        out << "Rut hom nay:        " << fixed << setprecision(2) << tongRutTrongNgay << " / "
            << BankConstants::HAN_MUC_RUT_NGAY_TOI_DA << " VND\n";
    }

    virtual void XuatThuocTinhRieng(ostream& out) const = 0;

    virtual void XuatThongTin(ostream& out) const {
        out << "---------------- THONG TIN TAI KHOAN ----------------\n";
        out << "Loai tai khoan:     " << getLoaiTaiKhoan() << '\n';
        XuatThongTinChung(out);
        XuatThuocTinhRieng(out);
        out << "-----------------------------------------------------\n";
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
                   to_string(static_cast<long long>(BankConstants::HAN_MUC_RUT_MOI_LAN_TOI_THIEU)) + " VND!";
            return false;
        }

        if (soTien > BankConstants::HAN_MUC_RUT_MOI_LAN_TOI_DA) {
            lyDo = "So tien rut vuot qua han muc 1 lan (toi da " +
                   to_string(static_cast<long long>(BankConstants::HAN_MUC_RUT_MOI_LAN_TOI_DA)) + " VND)!";
            return false;
        }

        if (tongRutTrongNgay + soTien > BankConstants::HAN_MUC_RUT_NGAY_TOI_DA) {
            lyDo = "Vuot qua tong han muc rut trong ngay (con lai: " +
                   to_string(static_cast<long long>(BankConstants::HAN_MUC_RUT_NGAY_TOI_DA - tongRutTrongNgay)) + " VND)!";
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
            lyDo += "\n[CANH BAO]: So du con lai (" + to_string(static_cast<long long>(sau)) +
                    " VND) da xuong duoi nguong canh bao (" +
                    to_string(static_cast<long long>(nguongCanhBaoSoDu)) + " VND)!";
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
            cout << "Tai khoan chua co giao dich nao duoc ghi nhan.\n";
            return;
        }

        cout << "\n============================== LICH SU GIAO DICH ==============================\n";
        cout << left << setw(22) << "MA GIAO DICH"
             << setw(20) << "THOI GIAN"
             << setw(22) << "LOAI GIAO DICH"
             << right << setw(19) << "SO TIEN"
             << setw(17) << "PHI"
             << setw(20) << "SO DU SAU\n";
        cout << string(100, '-') << "\n";

        // In nguoc tu cuoi ve dau de hien thi giao dich moi nhat truoc
        for (auto it = lichSuGiaoDich.rbegin(); it != lichSuGiaoDich.rend(); ++it) {
            it->InDongBang();
        }
        cout << string(100, '=') << "\n";
    }

    // Xem giao dich gan nhat
    void HienThiGiaoDichGanNhat() const {
        if (lichSuGiaoDich.empty()) {
            cout << "Chua co giao dich nao!\n";
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
        cout << "\n=== DANH SACH GIAO DICH THEO LOAI: " << loaiGDToString(loai) << " ===\n";
        bool co = false;
        for (auto it = lichSuGiaoDich.rbegin(); it != lichSuGiaoDich.rend(); ++it) {
            if (it->getLoai() == loai) {
                it->InDongBang();
                co = true;
            }
        }
        if (!co) {
            cout << "Khong tim thay giao dich phu hop.\n";
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
            f << "So du hien tai: " << fixed << setprecision(2) << soDu << " VND\n";
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

        if (!laSoHuuHan(laiSuat) || laiSuat < 0 || laiSuat > 100)
            throw invalid_argument("Lai suat phai tu 0 den 100%!");
    }

    void XuatThuocTinhRieng(ostream& out) const override {
        out << "Lai suat tiet kiem: " << fixed << setprecision(2) << laiSuat << " %/nam\n";
        out << "Tien lai 1 thang uoc tinh: " << fixed << setprecision(2) << TinhLaiHangThang() << " VND\n";
    }

public:
    TaiKhoanTietKiem(string soTK = "", string ten = "", double sd = 0, double ls = 0)
        : TaiKhoan(soTK, ten, sd), laiSuat(ls) {
        if (!laSoHuuHan(ls) || ls < 0 || ls > 100)
            throw invalid_argument("Lai suat khong hop le!");
        if (sd < 0)
            throw invalid_argument("Tai khoan tiet kiem khong duoc co so du am!");
    }

    double getLaiSuat() const { return laiSuat; }

    void setLaiSuat(double ls) {
        if (!laSoHuuHan(ls) || ls < 0 || ls > 100)
            throw invalid_argument("Lai suat phai tu 0 den 100%!");
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
        if (!(in >> hanMucTinDung)) {
            in.clear();
            in.ignore(numeric_limits<streamsize>::max(), '\n');
            throw invalid_argument("Han muc tin dung phai la mot con so hop le!");
        }
        in.ignore(numeric_limits<streamsize>::max(), '\n');

        if (!laSoHuuHan(hanMucTinDung) || hanMucTinDung < 0)
            throw invalid_argument("Han muc tin dung phai >= 0!");
    }

    void XuatThuocTinhRieng(ostream& out) const override {
        out << "Han muc tin dung:   " << fixed << setprecision(2) << hanMucTinDung << " VND\n";
        out << "So tien co the chi: " << fixed << setprecision(2) << getSoDuKhaDung() << " VND\n";
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
                   to_string(static_cast<long long>(getSoDuKhaDung())) + " VND)!";
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
                   to_string(static_cast<long long>(soTien)) + " VND + Phi: " +
                   to_string(static_cast<long long>(phi)) + " VND)!";
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
            lyDo += "\n[CANH BAO]: So du TK nguon (" + to_string(static_cast<long long>(sauNguon)) +
                    " VND) da xuong duoi nguong canh bao (" +
                    to_string(static_cast<long long>(nguon->getNguongCanhBao())) + " VND)!";
        }
        return true;
    }

    // ==================== TRA CUU VA THONG KE ====================

    void HienThiTatCaTaiKhoan() const {
        if (danhSachTaiKhoan.empty()) {
            cout << "He thong hien chua co tai khoan nao.\n";
            return;
        }

        cout << "\n======================== DANH SACH TAI KHOAN HE THONG ========================\n";
        cout << left << setw(5)  << "STT"
             << setw(16) << "SO TAI KHOAN"
             << setw(26) << "CHU TAI KHOAN"
             << setw(16) << "LOAI TK"
             << setw(16) << "TRANG THAI"
             << right << setw(18) << "SO DU THUC TE\n";
        cout << string(97, '-') << "\n";

        for (size_t i = 0; i < danhSachTaiKhoan.size(); ++i) {
            const auto& tk = danhSachTaiKhoan[i];
            cout << left << setw(5)  << (i + 1)
                 << setw(16) << tk->getSoTaiKhoan()
                 << setw(26) << tk->getTenChuTaiKhoan()
                 << setw(16) << tk->getLoaiTaiKhoan()
                 << setw(16) << tk->getTrangThaiString()
                 << right << setw(14) << fixed << setprecision(2) << tk->getSoDuCongKhai() << " VND\n";
        }
        cout << string(97, '=') << "\n";
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
                        cout << "-> Da cong " << fixed << setprecision(2) << gd.getSoTien()
                             << " VND vao TK " << tkTK->getSoTaiKhoan() << " (" << tkTK->getTenChuTaiKhoan() << ")\n";
                    }
                }
            }
        }

        cout << "\nKet toan hoan tat: Da cong lai cho " << dem
             << " tai khoan voi tong so tien: " << fixed << setprecision(2) << tongLai << " VND.\n";
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

        cout << "\n==================== BAO CAO THONG KE HE THONG NGAN HANG ====================\n";
        cout << "Tong so tai khoan:              " << danhSachTaiKhoan.size() << "\n";
        cout << " - So tai khoan dang hoat dong: " << soTKHoatDong << "\n";
        cout << " - So tai khoan dang bi khoa:   " << soTKBiKhoa << "\n";
        cout << " - So tai khoan da dong:        " << soTKDaDong << "\n";
        cout << "Tong so du tien gui khach hang: " << fixed << setprecision(2) << tongSoDu << " VND\n";
        cout << "Tong tien da nap vao he thong:  " << fixed << setprecision(2) << tongNap << " VND\n";
        cout << "Tong tien da rut khoi he thong: " << fixed << setprecision(2) << tongRut << " VND\n";
        cout << "Tong luong tien giao dich chuyen:" << fixed << setprecision(2) << tongChuyen << " VND\n";
        cout << "==============================================================================\n";
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
        cin.clear();
        cin.ignore(numeric_limits<streamsize>::max(), '\n');
        return -1;
    }
    cin.ignore(numeric_limits<streamsize>::max(), '\n');
    return luaChon;
}

double nhapSoTien(const string& nhan) {
    double soTien;
    while (true) {
        cout << nhan;
        if (cin >> soTien && laSoHuuHan(soTien) && soTien > 0) {
            cin.ignore(numeric_limits<streamsize>::max(), '\n');
            return soTien;
        }
        cout << "[Loi]: So tien nhap khong hop le! Vui long nhap so thuc duong huu han.\n";
        cin.clear();
        cin.ignore(numeric_limits<streamsize>::max(), '\n');
    }
}

string nhapChuoiKhongRong(const string& nhan) {
    string s;
    while (true) {
        cout << nhan;
        getline(cin, s);
        if (!s.empty()) return s;
        cout << "[Loi]: Du lieu khong duoc de trong! Vui long nhap lai.\n";
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
        cout << "\n--- TRA CUU LICH SU GIAO DICH ---\n";
        cout << "1. Xem toan bo lich su (moi nhat truoc)\n";
        cout << "2. Xem giao dich gan nhat\n";
        cout << "3. Tim kiem theo ma giao dich\n";
        cout << "4. Loc giao dich nap tien\n";
        cout << "5. Loc giao dich rut tien\n";
        cout << "6. Loc giao dich chuyen tien di / den\n";
        cout << "0. Quay lai menu tai khoan\n";
        cout << "Lua chon: ";
        chon = nhapLuaChonSo();

        switch (chon) {
            case 1:
                tk->HienThiLichSu();
                break;
            case 2:
                tk->HienThiGiaoDichGanNhat();
                break;
            case 3: {
                string maGD = nhapChuoiKhongRong("Nhap ma giao dich can tra cuu: ");
                GiaoDich gd;
                if (tk->TimGiaoDichTheoMa(maGD, gd)) {
                    cout << gd;
                } else {
                    cout << "Khong tim thay giao dich voi ma: " << maGD << "\n";
                }
                break;
            }
            case 4:
                tk->LocGiaoDichTheoLoai(LoaiGiaoDich::NAP_TIEN);
                break;
            case 5:
                tk->LocGiaoDichTheoLoai(LoaiGiaoDich::RUT_TIEN);
                break;
            case 6:
                tk->LocGiaoDichTheoLoai(LoaiGiaoDich::CHUYEN_TIEN_DI);
                tk->LocGiaoDichTheoLoai(LoaiGiaoDich::CHUYEN_TIEN_DEN);
                break;
            case 0:
                break;
            default:
                cout << "Lua chon khong hop le!\n";
        }
    } while (chon != 0);
}

// Menu danh cho khach hang da dang nhap thanh cong
void menuKhachHang(TaiKhoan* tk, NganHang& bank) {
    int chon;
    do {
        cout << "\n============================================================\n";
        cout << "   TAI KHOAN: " << tk->getSoTaiKhoan()
             << " | CHU TK: " << tk->getTenChuTaiKhoan()
             << " | LOAI: " << tk->getLoaiTaiKhoan() << "\n";
        cout << "============================================================\n";
        cout << "1. Xem thong tin tai khoan & So du kha dung\n";
        cout << "2. Nap tien vao tai khoan (Yeu cau PIN)\n";
        cout << "3. Rut tien tu tai khoan (Yeu cau PIN)\n";
        cout << "4. Chuyen tien den tai khoan khac (Yeu cau PIN)\n";
        cout << "5. Tra cuu lich su giao dich\n";
        cout << "6. Doi mat khau dang nhap\n";
        cout << "7. Doi ma PIN giao dich\n";
        cout << "8. Xuat sao ke ra file (TXT / CSV)\n";
        cout << "9. Cai dat nguong canh bao so du toi thieu\n";
        cout << "0. Dang xuat tai khoan\n";
        cout << "Lua chon cua ban: ";
        chon = nhapLuaChonSo();

        switch (chon) {
            case 1:
                tk->HienThiThongTin();
                break;

            case 2: {
                double soTien = nhapSoTien("Nhap so tien can nap (VND): ");
                string pin = nhapMaPIN("Nhap ma PIN giao dich: ");
                string lyDo;
                if (tk->ThucHienNapTien(soTien, pin, lyDo)) {
                    cout << "[Thanh cong]: " << lyDo << "\n";
                    cout << "So du hien tai: " << fixed << setprecision(2)
                         << tk->getSoDuCongKhai() << " VND\n";
                } else {
                    cout << "[That bai]: " << lyDo << "\n";
                }
                break;
            }

            case 3: {
                double soTien = nhapSoTien("Nhap so tien can rut (VND): ");
                string pin = nhapMaPIN("Nhap ma PIN giao dich: ");
                string lyDo;
                if (tk->ThucHienRutTien(soTien, pin, lyDo)) {
                    cout << "[Thanh cong]: " << lyDo << "\n";
                    cout << "So du con lai: " << fixed << setprecision(2)
                         << tk->getSoDuCongKhai() << " VND\n";
                } else {
                    cout << "[That bai]: " << lyDo << "\n";
                }
                break;
            }

            case 4: {
                string tkDich = nhapChuoiKhongRong("Nhap so tai khoan thu huong: ");
                double soTien = nhapSoTien("Nhap so tien muon chuyen (VND): ");
                cout << "Phi chuyen tien he thong: " << fixed << setprecision(2)
                     << BankConstants::PHI_CHUYEN_TIEN_CO_DINH << " VND\n";
                string pin = nhapMaPIN("Nhap ma PIN de xac thuc chuyen tien: ");
                string lyDo;
                if (bank.ChuyenTien(tk->getSoTaiKhoan(), tkDich, soTien, pin, lyDo)) {
                    cout << "[Thanh cong]: " << lyDo << "\n";
                    cout << "So du hien tai: " << fixed << setprecision(2)
                         << tk->getSoDuCongKhai() << " VND\n";
                } else {
                    cout << "[That bai]: " << lyDo << "\n";
                }
                break;
            }

            case 5:
                menuLichSuGiaoDich(tk);
                break;

            case 6: {
                string mkCu = NhapMatKhauAnToan("Nhap mat khau hien tai: ", 32);
                string mkMoi = NhapMatKhauAnToan("Nhap mat khau moi: ", 32);
                string xnMK = NhapMatKhauAnToan("Xac nhan mat khau moi: ", 32);
                string tb;
                if (tk->DoiMatKhau(mkCu, mkMoi, xnMK, tb)) {
                    cout << "[Thanh cong]: " << tb << "\n";
                } else {
                    cout << "[That bai]: " << tb << "\n";
                }
                break;
            }

            case 7: {
                string pinCu = nhapMaPIN("Nhap ma PIN hien tai: ");
                string pinMoi = nhapMaPIN("Nhap ma PIN moi (6 chu so): ");
                string xnPin = nhapMaPIN("Xac nhan ma PIN moi: ");
                string tb;
                if (tk->DoiPIN(pinCu, pinMoi, xnPin, tb)) {
                    cout << "[Thanh cong]: " << tb << "\n";
                } else {
                    cout << "[That bai]: " << tb << "\n";
                }
                break;
            }

            case 8: {
                cout << "Chon dinh dang xuat sao ke:\n";
                cout << "1. File van ban chi tiet (TXT)\n";
                cout << "2. File bang tinh (CSV)\n";
                cout << "Chon: ";
                int fChon = nhapLuaChonSo();
                string tenFileDefault = "SaoKe_" + tk->getSoTaiKhoan() + (fChon == 2 ? ".csv" : ".txt");
                cout << "Nhap ten file (mac dinh: " << tenFileDefault << "): ";
                string tenFile;
                getline(cin, tenFile);
                if (tenFile.empty()) tenFile = tenFileDefault;

                if (tk->XuatSaoKe(tenFile, fChon == 2)) {
                    cout << "[Thanh cong]: Da xuat sao ke tai khoan ra file \"" << tenFile << "\"!\n";
                } else {
                    cout << "[Loi]: Khong the ghi file \"" << tenFile << "\"!\n";
                }
                break;
            }

            case 9: {
                cout << "Nguong canh bao so du hien tai: " << fixed << setprecision(2)
                     << tk->getNguongCanhBao() << " VND\n";
                double nguongMoi = nhapSoTien("Nhap nguong canh bao so du moi (VND): ");
                tk->setNguongCanhBao(nguongMoi);
                cout << "[Thanh cong]: Da cap nhat nguong canh bao moi!\n";
                break;
            }

            case 0:
                cout << "Dang dang xuat khoi tai khoan...\n";
                break;

            default:
                cout << "Lua chon khong hop le!\n";
        }
    } while (chon != 0);
}

// Menu danh cho Quan tri vien he thong (Admin)
void menuQuanTri(NganHang& bank) {
    int chon;
    do {
        cout << "\n============================================================\n";
        cout << "                MENU QUAN TRI VIEN (ADMIN)                  \n";
        cout << "============================================================\n";
        cout << "1. Hien thi danh sach tat ca tai khoan\n";
        cout << "2. Tim kiem tai khoan (theo So TK hoac Ten chu TK)\n";
        cout << "3. Tim tai khoan co so du lon nhat he thong\n";
        cout << "4. Khoa / Mo khoa / Dong tai khoan khach hang\n";
        cout << "5. Tinh va ket toan lai tiet kiem hang thang\n";
        cout << "6. Bao cao thong ke toan ngan hang\n";
        cout << "7. Tra cuu giao dich theo ma toan he thong\n";
        cout << "8. Luu du lieu toan he thong ra file\n";
        cout << "9. Tai lai du lieu he thong tu file\n";
        cout << "0. Dang xuat quan tri vien\n";
        cout << "Lua chon: ";
        chon = nhapLuaChonSo();

        switch (chon) {
            case 1:
                bank.HienThiTatCaTaiKhoan();
                break;

            case 2: {
                string tuKhoa = nhapChuoiKhongRong("Nhap so TK hoac ten chu tai khoan: ");
                bank.TimKiemTaiKhoan(tuKhoa);
                break;
            }

            case 3:
                bank.TimTaiKhoanSoDuLonNhat();
                break;

            case 4: {
                string soTK = nhapChuoiKhongRong("Nhap so tai khoan can thao tac: ");
                TaiKhoan* tk = bank.getTaiKhoanPtr(soTK);
                if (!tk) {
                    cout << "[Loi]: Khong tim thay tai khoan voi so TK: " << soTK << "\n";
                    break;
                }

                cout << "Trang thai hien tai: " << tk->getTrangThaiString() << "\n";
                cout << "Chon hanh dong:\n";
                cout << "1. Mo khoa tai khoan (ACTIVE) & reset so lan sai MK/PIN\n";
                cout << "2. Khoa tai khoan (LOCKED)\n";
                cout << "3. Dong tai khoan (CLOSED)\n";
                cout << "0. Huy bo\n";
                cout << "Chon: ";
                int act = nhapLuaChonSo();

                if (act == 1) {
                    tk->MoKhoa();
                    cout << "[Thanh cong]: Tai khoan " << soTK << " da duoc MO KHOA thanh cong!\n";
                } else if (act == 2) {
                    tk->KhoaTaiKhoan();
                    cout << "[Thanh cong]: Tai khoan " << soTK << " da bi KHOA!\n";
                } else if (act == 3) {
                    tk->DongTaiKhoan();
                    cout << "[Thanh cong]: Tai khoan " << soTK << " da bi DONG!\n";
                }
                break;
            }

            case 5:
                bank.TinhVaCongLaiTietKiem();
                break;

            case 6:
                bank.BaoCaoThongKe();
                break;

            case 7: {
                string maGD = nhapChuoiKhongRong("Nhap ma giao dich: ");
                bank.TraCuuGiaoDichToanHeThong(maGD);
                break;
            }

            case 8: {
                cout << "Nhap ten file luu du lieu (mac dinh: " << BankConstants::FILE_DU_LIEU_MAC_DINH << "): ";
                string fn;
                getline(cin, fn);
                if (fn.empty()) fn = BankConstants::FILE_DU_LIEU_MAC_DINH;
                if (bank.LuuDuLieu(fn)) {
                    cout << "[Thanh cong]: Da luu toan bo du lieu ra file \"" << fn << "\"!\n";
                } else {
                    cout << "[Loi]: Khong the luu du lieu vao file \"" << fn << "\"!\n";
                }
                break;
            }

            case 9: {
                cout << "Nhap ten file nap du lieu (mac dinh: " << BankConstants::FILE_DU_LIEU_MAC_DINH << "): ";
                string fn;
                getline(cin, fn);
                if (fn.empty()) fn = BankConstants::FILE_DU_LIEU_MAC_DINH;
                if (bank.TaiDuLieu(fn)) {
                    cout << "[Thanh cong]: Da tai du lieu tu file \"" << fn << "\" thanh cong!\n";
                } else {
                    cout << "[Loi]: Khong the doc du lieu tu file \"" << fn << "\"!\n";
                }
                break;
            }

            case 0:
                cout << "Dang thoat quyen quan tri vien...\n";
                break;

            default:
                cout << "Lua chon khong hop le!\n";
        }
    } while (chon != 0);
}

// Menu chinh cua he thong
void hienThiMenuChinh() {
    cout << "\n============================================================\n";
    cout << "           HE THONG QUAN LY TAI KHOAN NGAN HANG             \n";
    cout << "============================================================\n";
    cout << "1. Dang nhap tai khoan khach hang\n";
    cout << "2. Dang ky mo tai khoan tiet kiem\n";
    cout << "3. Dang ky mo tai khoan thanh toan\n";
    cout << "4. Dang nhap quan tri vien (Admin)\n";
    cout << "5. Huong dan su dung & Gioi han bao mat demo\n";
    cout << "0. Thoat chuong trinh\n";
    cout << "Lua chon cua ban: ";
}

void hienThiThongTinBaoMatDemo() {
    cout << "\n================== CHINH SACH BAO MAT & HUONG DAN ==================\n";
    cout << "1. QUY TAC MAT KHAU & PIN:\n";
    cout << "   - Mat khau va PIN duoc quan ly doc lap, khong bao gio luu o dang ro.\n";
    cout << "   - Thuat toan bam: SHA-256 kem Per-Account Salt ngau nhien cho tung TK.\n";
    cout << "   - Ma PIN bat buoc gom dung 6 chu so (giu nguyen so 0 o dau, vi du: 012345).\n";
    cout << "2. QUY TAC KHOA TAI KHOAN:\n";
    cout << "   - Nhap sai mat khau 5 lan -> Tai khoan bi KHOA dang nhap.\n";
    cout << "   - Nhap sai ma PIN 3 lan   -> Tai khoan bi KHOA giao dich.\n";
    cout << "   - Chi co Quan tri vien (Admin) moi co tham quyen mo khoa tai khoan.\n";
    cout << "3. TAI KHOAN ADMIN DEMO:\n";
    cout << "   - Tai khoan: admin\n";
    cout << "   - Mat khau : admin123\n";
    cout << "4. GIOI HAN BAO MAT MO HINH DEMO:\n";
    cout << "   - Chuong trinh bam mat khau/PIN bang SHA-256 hop chuan trong C++.\n";
    cout << "   - Tuy nhien, trong moi truong console C++, chua co co che vung nho an toan\n";
    cout << "     (nhu Secure Enclave hoac OS DPAPI) de xoa sach bo nho RAM khi thoat.\n";
    cout << "   - File luu tru du lieu ghi nhan cac ma bam SHA-256 salt, tuy nhien can duoc\n";
    cout << "     bao ve quyen doc tren he thong file cua he dieu hanh.\n";
    cout << "====================================================================\n";
}

// ============================================================================
// HAM MAIN (DIEM KHOI DAU CHUONG TRINH)
// ============================================================================
int main() {
    NganHang bank;

    // Tu dong tai du lieu tu file neu ton tai
    if (bank.TaiDuLieu(BankConstants::FILE_DU_LIEU_MAC_DINH)) {
        cout << "[He thong]: Da tu dong nap du lieu tu \""
             << BankConstants::FILE_DU_LIEU_MAC_DINH << "\".\n";
    }

    int luaChon;
    do {
        hienThiMenuChinh();
        luaChon = nhapLuaChonSo();

        try {
            switch (luaChon) {
                case 1: {
                    // Dang nhap tai khoan khach hang
                    cout << "\n--- DANG NHAP TAI KHOAN ---\n";
                    string soTK = nhapChuoiKhongRong("Nhap so tai khoan: ");
                    string matKhau = NhapMatKhauAnToan("Nhap mat khau: ", 32);

                    string thongBaoLoi;
                    TaiKhoan* tk = bank.DangNhap(soTK, matKhau, thongBaoLoi);
                    if (tk) {
                        cout << "[Dang nhap thanh cong] Xin chao, " << tk->getTenChuTaiKhoan() << "!\n";
                        menuKhachHang(tk, bank);
                    } else {
                        cout << "[Loi dang nhap]: " << thongBaoLoi << "\n";
                    }
                    break;
                }

                case 2:
                case 3: {
                    // Mo tai khoan moi
                    cout << "\n--- DANG KY MO TAI KHOAN "
                         << (luaChon == 2 ? "TIET KIEM" : "THANH TOAN") << " ---\n";

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
                        cout << "[Thanh cong]: " << lyDo << "\n";
                    } else {
                        cout << "[Loi]: " << lyDo << "\n";
                    }
                    break;
                }

                case 4: {
                    // Dang nhap Admin
                    cout << "\n--- DANG NHAP QUAN TRI VIEN (ADMIN) ---\n";
                    string user = nhapChuoiKhongRong("Ten dang nhap quan tri: ");
                    string pass = NhapMatKhauAnToan("Mat khau quan tri: ", 32);

                    if (bank.XacThucAdmin(user, pass)) {
                        cout << "[Thanh cong]: Dang nhap quyen Quan tri vien thanh cong!\n";
                        menuQuanTri(bank);
                    } else {
                        cout << "[Loi]: Thong tin quan tri vien khong chinh xac!\n";
                    }
                    break;
                }

                case 5:
                    hienThiThongTinBaoMatDemo();
                    break;

                case 0: {
                    cout << "Tu dong sao luu du lieu he thong truoc khi thoat...\n";
                    if (bank.LuuDuLieu(BankConstants::FILE_DU_LIEU_MAC_DINH)) {
                        cout << "Da luu du lieu an toan vao \""
                             << BankConstants::FILE_DU_LIEU_MAC_DINH << "\".\n";
                    }
                    cout << "Cam on ban da su dung chuong trinh Quan ly Ngan hang!\n";
                    break;
                }

                default:
                    cout << "Lua chon khong hop le! Vui long chon cac chuc nang tu 0 den 5.\n";
            }
        } catch (const exception& e) {
            cout << "\n[Ngoai le bat duoc]: " << e.what() << "\n";
        }

    } while (luaChon != 0);

    return 0;
}

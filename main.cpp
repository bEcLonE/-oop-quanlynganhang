/**
 * ============================================================================
 * CHUONG TRINH QUAN LY TAI KHOAN NGAN HANG (C++ OOP)
 * Mon hoc: Lap trinh huong doi tuong (Object-Oriented Programming)
 * 
 * CAC NGUYEN TAC THIET KE OOP & TINH NANG:
 * 1. Dong goi (Encapsulation):
 *    - Day du cac phuong thuc Getter / Setter cho cac lop NganHang, TaiKhoan, GiaoDich.
 * 2. Ke thua (Inheritance):
 *    - Lop co so truu tuong TaiKhoan.
 *    - Lop dan xuat TaiKhoanTietKiem (bo sung lai suat %/nam).
 *    - Lop dan xuat TaiKhoanThanhToan (bo sung han muc tin dung).
 * 3. Da hinh (Polymorphism) - TRONG TAM CHUYEN SAU VAO CHUC NANG RUT TIEN:
 *    - Phuong thuc thuan ao: CoTheRut(), RutTien(), getSoDuKhaDung(), HienThiThongTin(), getLoaiTaiKhoan().
 *    - Quy tac rut tien da hinh:
 *      + TaiKhoanTietKiem: Khong duoc rut qua so du hien co (so du luon >= 0).
 *      + TaiKhoanThanhToan: Cho phep rut am trong pham vi han muc tin dung (so du am toi da -hanMucTinDung).
 *    - Kiem tra han muc rut tien theo quy dinh: toi thieu 50.000 VND/lan, toi da 20.000.000 VND/lan, toi da 50.000.000 VND/ngay.
 * 4. Nap chong toan tu (Operator Overloading):
 *    - operator>> va operator<< cho TaiKhoan va GiaoDich.
 * 5. Quan ly bo nho an toan:
 *    - Su dung std::unique_ptr<TaiKhoan> va std::vector de tranh ro ri bo nho.
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
    const double NGUONG_CANH_BAO_MAC_DINH    = 50000.0;    // 50.000 VND
    const int    MAX_SAI_MAT_KHAU            = 5;          // Khoa sau 5 lan sai MK
    const string FILE_DU_LIEU_MAC_DINH       = "bank_data.txt";
}

// ============================================================================
// CAC TIEN ICH KIEM TRA VA DINH DANG DU LIEU
// ============================================================================

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

// Dinh dang so tien voi dau phan cach hang nghin, hang trieu (VD: 1,250,000 VND)
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

void printDivider(int width = 72, char ch = '-') {
    cout << UI::cyan() << string(width, ch) << UI::reset() << "\n";
}

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

// ============================================================================
// ENUM TRANG THAI TAI KHOAN VA LOAI GIAO DICH
// ============================================================================
enum class TrangThaiTaiKhoan {
    ACTIVE,
    LOCKED,
    CLOSED
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
    RUT_TIEN
};

inline string loaiGDToString(LoaiGiaoDich loai) {
    switch (loai) {
        case LoaiGiaoDich::NAP_TIEN: return "Nap tien";
        case LoaiGiaoDich::RUT_TIEN: return "Rut tien";
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
    string trangThai;
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

    // Getter
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

    // Setter
    void setMaGiaoDich(string maGD) { maGiaoDich=maGD; }
    void setLoai(LoaiGiaoDich l) { loai=l; }
    void setSoTaiKhoanNguon(string nguon) { soTaiKhoanNguon=nguon; }
    void setSoTaiKhoanDich(string dich) { soTaiKhoanDich=dich; }
    void setSoTien(double tien) { soTien=tien; }
    void setPhiGiaoDich(double phi) { phiGiaoDich=phi; }
    void setThoiGian(string tg) { thoiGian=tg; }
    void setSoDuTruoc(double truoc) { soDuTruoc=truoc; }
    void setSoDuSau(double sau)  { soDuSau=sau; }
    void setTrangThai(string tt) { trangThai=tt; }
    void setNoiDung(string nd) { noiDung=nd; }

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
// HAM NHAP MAT KHAU AN TOAN (AN KY TU BANG '*')
// ============================================================================
string NhapMatKhauAnToan(const string& prompt) {
    while (true) {
        cout << prompt << flush;
        string res = "";

#ifdef _WIN32
        if (!_isatty(_fileno(stdin))) {
            if (!getline(cin, res)) return "";
            if (!res.empty() && res.back() == '\r') res.pop_back();
        } else {
            while (true) {
                int ch = _getch();
                if (ch == 0 || ch == 224) {
                    _getch();
                    continue;
                }
                if (ch == 13 || ch == 10) {
                    cout << "\n";
                    break;
                }
                if (ch == 8) {
                    if (!res.empty()) {
                        res.pop_back();
                        cout << "\b \b" << flush;
                    }
                    continue;
                }
                if (ch == 3 || ch == 26) {
                    cout << "\n";
                    return "";
                }
                if (ch < 32 || ch > 126) {
                    continue;
                }
                res.push_back(static_cast<char>(ch));
                cout << '*' << flush;
            }
        }
#else
        if (!getline(cin, res)) return "";
#endif

        if (res.empty()) {
            if (cin.eof() || cin.fail()) return "";
            cout << "[Loi]: Du lieu khong duoc de trong! Vui long nhap lai.\n";
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
    string matKhauHash;
    string pinHash;
    string salt;
    TrangThaiTaiKhoan trangThai;
    int soLanDangNhapSai;
    int soLanNhapPinSai;
    double nguongCanhBaoSoDu;
    double tongRutTrongNgay;
    string ngayGiaoDichHienTai;
    vector<GiaoDich> lichSuGiaoDich;

public:
    TaiKhoan(string soTK = "", string ten = "", double sd = 0)
        : soTaiKhoan(soTK), tenChuTaiKhoan(ten), soDu(sd),
          matKhauHash(""), pinHash(""), salt(""),
          trangThai(TrangThaiTaiKhoan::ACTIVE),
          soLanDangNhapSai(0), soLanNhapPinSai(0),
          nguongCanhBaoSoDu(BankConstants::NGUONG_CANH_BAO_MAC_DINH),
          tongRutTrongNgay(0.0), ngayGiaoDichHienTai(layNgayHienTai()) {
        if (!laSoHuuHan(sd))
            throw invalid_argument("So du khoi tao phai la so thuc huu han!");
    }

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
    double gettongruttrongngay() const { return tongRutTrongNgay; }
    string getngaygiaodichhientai() const { return ngayGiaoDichHienTai; }
    double getTongRutTrongNgay() const { return tongRutTrongNgay; }
    string getNgayGiaoDichHienTai() const { return ngayGiaoDichHienTai; }
    double getSoDuCongKhai() const { return soDu;}
    double getSoDu() const { return soDu; }

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

    void setmatkhauhash(string mkHash) {
        matKhauHash=mkHash; 
    }
    void setpinhash(string pin_h){
        pinHash=pin_h;
    }
    void set_salt(string s){
        salt=s;
    }
    void setsolandangnhapsai(int sldns){
        soLanDangNhapSai=sldns;
    }
    void setsolannhappinsai(int slnps){
        soLanNhapPinSai=slnps;
    }
    void settongruttrongngay(double rtn){
        tongRutTrongNgay=rtn;
    }
    void setngaygiaodichhientai(string ngay){
        ngayGiaoDichHienTai=ngay;
    }
    void setLichSuGiaoDich(const vector<GiaoDich>& lichSu) {
        lichSuGiaoDich = lichSu;
    }

    void setSoDu(double soDuMoi) {
        if (!laSoHuuHan(soDuMoi))
            throw invalid_argument("So du khong hop le!");
        soDu = soDuMoi;
    }

    // Nhap xuat thong tin
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

    virtual void NhapThuocTinhRieng(istream& in) = 0;

    void NhapThongTinBaoMat() {
        string mk = NhapMatKhauAnToan("Thiet lap mat khau dang nhap: ");
        string xnMK = NhapMatKhauAnToan("Xac nhan mat khau: ");
        if (mk != xnMK) {
            throw invalid_argument("Xac nhan mat khau khong khop!");
        }
        DatMatKhau(mk);
    }

    virtual void NhapThongTin(istream& in) {
        NhapThongTinChung(in);
        NhapThuocTinhRieng(in);
        NhapThongTinBaoMat();
    }

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

    // ==================== QUAN LY MAT KHAU VA XAC THUC ====================

    void DatMatKhau(const string& mk) {
        matKhauHash = mk;
        soLanDangNhapSai = 0;
    }

    bool XacThucMatKhau(const string& mk, string& thongBaoLoi) {
        if (trangThai == TrangThaiTaiKhoan::CLOSED) {
            thongBaoLoi = "Tai khoan nay da bi dong!";
            return false;
        }
        if (trangThai == TrangThaiTaiKhoan::LOCKED) {
            thongBaoLoi = "Tai khoan dang bi khoa! Vui long lien he Quan tri vien de mo khoa.";
            return false;
        }

        if (mk == matKhauHash) {
            soLanDangNhapSai = 0;
            return true;
        }

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

    bool DoiMatKhau(const string& mkCu, const string& mkMoi, const string& xacNhanMoi, string& thongBao) {
        if (trangThai != TrangThaiTaiKhoan::ACTIVE) {
            thongBao = "Tai khoan khong o trang thai hoat dong de doi mat khau!";
            return false;
        }
        if (mkCu != matKhauHash) {
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

        matKhauHash = mkMoi;
        soLanDangNhapSai = 0;
        thongBao = "Doi mat khau dang nhap thanh cong!";
        return true;
    }

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
    virtual bool RutTien(double soTien) = 0;
    virtual double getSoDuKhaDung() const = 0;
    virtual void HienThiThongTin() const = 0;
    virtual string getLoaiTaiKhoan() const = 0;

    virtual bool NapTien(double soTien) {
        if (!laSoHuuHan(soTien) || soTien <= 0)
            return false;
        if (soDu > numeric_limits<double>::max() - soTien)
            return false;
        soDu += soTien;
        return true;
    }

    // ==================== CHUYEN SAU: CHUC NANG RUT TIEN ====================

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

    /**
     * Chuc nang Rut tien trung tam (khong can PIN):
     */
    bool ThucHienRutTien(double soTien, string& lyDo) {
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

        double truoc = soDu;
        if (!RutTien(soTien)) {
            lyDo = "Giao dich rut tien that bai do loi he thong!";
            return false;
        }
        double sau = soDu;
        GhiNhanRutTrongNgay(soTien);

        GiaoDich gd(taoMaGiaoDich(), LoaiGiaoDich::RUT_TIEN, soTaiKhoan, "",
                   soTien, 0.0, layThoiGianHienTai(), truoc, sau, "THANH_CONG", "Rut tien mat");
        lichSuGiaoDich.push_back(gd);

        lyDo = "Rut tien thanh cong!";
        if (sau < nguongCanhBaoSoDu) {
            lyDo += "\n[CANH BAO]: So du con lai (" + formatMoney(sau) +
                    ") da xuong duoi nguong canh bao (" +
                    formatMoney(nguongCanhBaoSoDu) + ")!";
        }
        return true;
    }

    bool ThucHienNapTien(double soTien, string& lyDo) {
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

        double truoc = soDu;
        if (!NapTien(soTien)) {
            lyDo = "Loi tran so du he thong!";
            return false;
        }
        double sau = soDu;

        GiaoDich gd(taoMaGiaoDich(), LoaiGiaoDich::NAP_TIEN, soTaiKhoan, "",
                   soTien, 0.0, layThoiGianHienTai(), truoc, sau, "THANH_CONG", "Nap tien vao tai khoan");
        lichSuGiaoDich.push_back(gd);

        lyDo = "Nap tien thanh cong!";
        return true;
    }

    void ThemGiaoDich(const GiaoDich& gd) {
        lichSuGiaoDich.push_back(gd);
    }

    friend class NganHang;

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
    double laiSuat; // %/nam

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

    // Quy tac rut tien da hinh: Tai khoan tiet kiem khong duoc phep rut am
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

    double TinhLaiHangThang() const {
        return getSoDu() * (laiSuat / 100.0) / 12.0;
    }
};

// ============================================================================
// LOP DAN XUAT: TAI KHOAN THANH TOAN
// ============================================================================
class TaiKhoanThanhToan : public TaiKhoan {
private:
    double hanMucTinDung;

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

    // Quy tac rut tien da hinh: Tai khoan thanh toan cho phep rut am trong han muc tin dung
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
// ============================================================================
class NganHang {
private:
    vector<unique_ptr<TaiKhoan>> danhSachTaiKhoan;
    string adminUsername;
    string adminPasswordHash;
    string adminSalt;

public:
    NganHang() {
        adminUsername = "admin";
        adminPasswordHash = "admin123";
        adminSalt = "";
    }

    // Getter 
    const vector<unique_ptr<TaiKhoan>>& getDanhSachTaiKhoan() const {
        return danhSachTaiKhoan;
    }
    string getAdminUsername() const {
        return adminUsername;
    }
    string getAdminPasswordHash() const {
        return adminPasswordHash;
    }
    string getAdminSalt() const {
        return adminSalt;
    }
    
    // Setter cho adminPasswordHash
    void setDanhSachTaiKhoan(vector<unique_ptr<TaiKhoan>> ds) {
        danhSachTaiKhoan = move(ds);
    }
    void setAdminUsername(const string& username) {
        adminUsername = username;
    }
    void setAdminPasswordHash(const string& passwordHash) {
        adminPasswordHash = passwordHash;
    }
    void setAdminSalt(const string& salt) {
        adminSalt = salt;
    }

    bool XacThucAdmin(const string& user, const string& pass) const {
        return (user == adminUsername && pass == adminPasswordHash);
    }

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

    bool LuuDuLieu(const string& tenFile = BankConstants::FILE_DU_LIEU_MAC_DINH) const {
        ofstream out(tenFile);
        if (!out.is_open()) return false;

        out << "# NGAN HANG DU LIEU - PHIEN BAN CHUAN HOA\n";
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
                << tk->getMatKhauHash() << "|"
                << tk->getPinHash() << "|"
                << tk->getSalt() << "|"
                << static_cast<int>(tk->getTrangThai()) << "|"
                << tk->getSoLanDangNhapSai() << "|"
                << tk->getSoLanNhapPinSai() << "|"
                << tk->getNguongCanhBao() << "|"
                << tk->getTongRutTrongNgay() << "|"
                << tk->getNgayGiaoDichHienTai() << "\n";

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
                vector<string> parts;
                string p;
                while (getline(ss, p, '|')) {
                    parts.push_back(p);
                }

                if (parts.size() >= 10) {
                    string loai = parts[0];
                    string soTK = parts[1];
                    string ten = parts[2];
                    double soDu = stod(parts[3]);
                    double thuocTinh = stod(parts[4]);
                    string mk = parts[5];
                    string pin = "";
                    string s = "";
                    TrangThaiTaiKhoan tt = TrangThaiTaiKhoan::ACTIVE;
                    int saiMK = 0;
                    int saiPIN = 0;
                    double nguong = BankConstants::NGUONG_CANH_BAO_MAC_DINH;
                    double rutNgay = 0.0;
                    string ngayGD = layNgayHienTai();

                    if (parts.size() >= 15) {
                        mk = parts[5];
                        pin = parts[6];
                        s = parts[7];
                        tt = static_cast<TrangThaiTaiKhoan>(stoi(parts[8]));
                        saiMK = stoi(parts[9]);
                        saiPIN = stoi(parts[10]);
                        nguong = stod(parts[11]);
                        rutNgay = stod(parts[12]);
                        ngayGD = parts[13];
                    } else if (parts.size() >= 14) {
                        s = parts[5];
                        mk = parts[6];
                        pin = parts[7];
                        tt = static_cast<TrangThaiTaiKhoan>(stoi(parts[8]));
                        saiMK = stoi(parts[9]);
                        saiPIN = stoi(parts[10]);
                        nguong = stod(parts[11]);
                        rutNgay = stod(parts[12]);
                        ngayGD = parts[13];
                    } else {
                        tt = static_cast<TrangThaiTaiKhoan>(stoi(parts[6]));
                        saiMK = stoi(parts[7]);
                        nguong = stod(parts[8]);
                        rutNgay = stod(parts[9]);
                        if (parts.size() > 10) ngayGD = parts[10];
                    }

                    unique_ptr<TaiKhoan> tk;
                    if (loai == "Tiet kiem") {
                        tk = make_unique<TaiKhoanTietKiem>(soTK, ten, soDu, thuocTinh);
                    } else {
                        tk = make_unique<TaiKhoanThanhToan>(soTK, ten, soDu, thuocTinh);
                    }

                    tk->setmatkhauhash(mk);
                    tk->setpinhash(pin);
                    tk->set_salt(s);
                    tk->setTrangThai(tt);
                    tk->setsolandangnhapsai(saiMK);
                    tk->setsolannhappinsai(saiPIN);
                    tk->setNguongCanhBao(nguong);
                    tk->settongruttrongngay(rutNgay);
                    tk->setngaygiaodichhientai(ngayGD);

                    danhSachTaiKhoan.push_back(move(tk));
                }
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

// ============================================================================
// MENU CONSOLE VA DIEU HUONG
// ============================================================================

// Menu danh cho khach hang da dang nhap thanh cong (khong co chuyen tien hay tra cuu lich su)
void menuKhachHang(TaiKhoan* tk) {
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
        cout << "  " << UI::cyan() << "[2]" << UI::reset() << " Nap tien vao tai khoan\n";
        cout << "  " << UI::cyan() << "[3]" << UI::reset() << " Rut tien tu tai khoan\n";
        cout << "  " << UI::cyan() << "[4]" << UI::reset() << " Doi mat khau dang nhap\n";
        cout << "  " << UI::cyan() << "[5]" << UI::reset() << " Cai dat nguong canh bao so du toi thieu\n";
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
                string lyDo;
                if (tk->ThucHienNapTien(soTien, lyDo)) {
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
                printBanner("RUT TIEN MAT", "Tap trung chuc nang rut tien");
                cout << "  Loai tai khoan: " << UI::yellow() << tk->getLoaiTaiKhoan() << UI::reset() << "\n";
                cout << "  So du thuc te:  " << UI::cyan() << formatMoney(tk->getSoDuCongKhai()) << UI::reset() << "\n";
                cout << "  So du kha dung: " << UI::green() << formatMoney(tk->getSoDuKhaDung()) << UI::reset() << "\n";
                cout << "  Han muc rut:    Toi thieu " << formatMoney(BankConstants::HAN_MUC_RUT_MOI_LAN_TOI_THIEU)
                     << " | Toi da " << formatMoney(BankConstants::HAN_MUC_RUT_MOI_LAN_TOI_DA) << "/lan\n";
                cout << "  Rut hom nay:    " << formatMoney(tk->gettongruttrongngay())
                     << " / " << formatMoney(BankConstants::HAN_MUC_RUT_NGAY_TOI_DA) << "\n\n";

                double soTien = nhapSoTien("Nhap so tien can rut (VND) [Nhap 0 de huy]: ", true);
                if (soTien == 0.0) {
                    showWarning("Da huy thao tac rut tien.");
                    pauseScreen();
                    break;
                }

                string lyDo;
                if (tk->ThucHienRutTien(soTien, lyDo)) {
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
                printBanner("DOI MAT KHAU DANG NHAP");
                string mkCu = NhapMatKhauAnToan("Nhap mat khau hien tai (Enter de huy): ");
                if (mkCu.empty()) {
                    showWarning("Da huy doi mat khau.");
                    pauseScreen();
                    break;
                }
                string mkMoi = NhapMatKhauAnToan("Nhap mat khau moi: ");
                if (mkMoi.empty()) {
                    showWarning("Da huy doi mat khau.");
                    pauseScreen();
                    break;
                }
                string xnMK = NhapMatKhauAnToan("Xac nhan mat khau moi: ");
                string tb;
                if (tk->DoiMatKhau(mkCu, mkMoi, xnMK, tb)) {
                    showSuccess(tb);
                } else {
                    showError(tb);
                }
                pauseScreen();
                break;
            }

            case 5: {
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
        printBanner("MENU QUAN TRI VIEN (ADMIN)", "Quan tri he thong");
        cout << "  " << UI::cyan() << "[1]" << UI::reset() << " Hien thi danh sach tat ca tai khoan\n";
        cout << "  " << UI::cyan() << "[2]" << UI::reset() << " Tim kiem tai khoan (theo So TK hoac Ten chu TK)\n";
        cout << "  " << UI::cyan() << "[3]" << UI::reset() << " Khoa / Mo khoa / Dong tai khoan khach hang\n";
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

            case 3: {
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
                cout << "  " << UI::cyan() << "[1]" << UI::reset() << " Mo khoa tai khoan (ACTIVE) & reset so lan sai MK\n";
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
    cout << "  " << UI::cyan() << "[5]" << UI::reset() << " Huong dan su dung & Quy dinh rut tien\n";
    cout << "  " << UI::red()  << "[0]" << UI::reset() << " Thoat chuong trinh\n";
    printDivider(72);
    cout << UI::bold() << "Lua chon cua ban: " << UI::reset();
}

void hienThiThongTinBaoMatDemo() {
    printBanner("QUY DINH RUT TIEN & HUONG DAN SU DUNG", "LAUDAITINHAI BANK Guidelines");
    cout << "  " << UI::bold() << "1. QUY TAC DANG NHAP & MAT KHAU:" << UI::reset() << "\n";
    cout << "     - Nhap mat khau duoc che ky tu an toan bang dau '*'.\n";
    cout << "     - Nhap sai mat khau qua 5 lan -> Tai khoan bi KHOA tu dong.\n";
    cout << "     - Quan tri vien (Admin) co quyen mo khoa tai khoan.\n\n";
    cout << "  " << UI::bold() << "2. QUY DINH CHUC NANG RUT TIEN:" << UI::reset() << "\n";
    cout << "     - Toi thieu moi lan rut : " << formatMoney(BankConstants::HAN_MUC_RUT_MOI_LAN_TOI_THIEU) << "\n";
    cout << "     - Toi da moi lan rut    : " << formatMoney(BankConstants::HAN_MUC_RUT_MOI_LAN_TOI_DA) << "\n";
    cout << "     - Toi da trong 1 ngay   : " << formatMoney(BankConstants::HAN_MUC_RUT_NGAY_TOI_DA) << "\n";
    cout << "     - Tai khoan Tiet kiem   : Khong duoc phep rut vuot qua so du (so du >= 0).\n";
    cout << "     - Tai khoan Thanh toan  : Cho phep rut am trong pham vi han muc tin dung.\n\n";
    cout << "  " << UI::bold() << "3. TAI KHOAN ADMIN DEMO:" << UI::reset() << "\n";
    cout << "     - Tai khoan: " << UI::cyan() << "admin" << UI::reset() << "\n";
    cout << "     - Mat khau : " << UI::cyan() << "admin123" << UI::reset() << "\n";
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
                        string matKhau = NhapMatKhauAnToan("Nhap mat khau: ");
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
                            menuKhachHang(tk);
                            break;
                        }

                        cout << UI::red() << "[Loi dang nhap]: " << thongBaoLoi << "\n" << UI::reset();

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
                    clearScreen();
                    printBanner(luaChon == 2 ? "DANG KY MO TAI KHOAN TIET KIEM" : "DANG KY MO TAI KHOAN THANH TOAN");

                    unique_ptr<TaiKhoan> tk;
                    if (luaChon == 2) {
                        tk = make_unique<TaiKhoanTietKiem>();
                    } else {
                        tk = make_unique<TaiKhoanThanhToan>();
                    }

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
                    clearScreen();
                    printBanner("DANG NHAP QUAN TRI VIEN (ADMIN)");
                    string user = nhapChuoiKhongRong("Ten dang nhap quan tri (hoac 0 de huy): ");
                    if (user == "0") {
                        showWarning("Da huy dang nhap quan tri.");
                        pauseScreen();
                        break;
                    }
                    string pass = NhapMatKhauAnToan("Mat khau quan tri: ");

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

#include <iostream>
#include <vector>
#include <string>
#include <algorithm>
#include <chrono>
#include <climits>
#include <cmath>
#include <unordered_map>
#include <random>
#include <cstring>

using namespace std;

// Piece movement directions
const int drW[] = {1, -1, 0, 0};
const int dcW[] = {0, 0, 1, -1};
const int drF[] = {1, 1, -1, -1};
const int dcF[] = {1, -1, 1, -1};
const int drN[] = {1, 1, -1, -1, 2, 2, -2, -2};
const int dcN[] = {2, -2, 2, -2, 1, -1, 1, -1};
const int drD[] = {0, 0, 2, -2};
const int dcD[] = {2, -2, 0, 0};
const int drA[] = {2, 2, -2, -2};
const int dcA[] = {2, -2, 2, -2};

// Piece values
const int PIECE_VALUES[] = {10000, 500, 400, 300, 200}; // W, N, F, D, A

// Evaluation constants
const int CENTER_BONUS = 30;
const int DEVELOPMENT_BONUS = 15;
const int KING_SAFETY_BONUS = 100;
const int MOBILITY_BONUS = 5;
const int DEFENSE_BONUS = 10;
const int THREAT_BONUS = 18;
const int TEMPO_BONUS = 12;
const int CHECK_BONUS = 160;
const int REVIVAL_HOLDING_BONUS = 40;

// Search constants
const int MAX_DEPTH = 32;
const size_t TT_SIZE = 1 << 21; // 2M entries (~64 MB)

// Optimized opening book for better bot performance
// Each string must have: 1W + 1N + 2F + 4D + 8A = 16 pieces
const string OPENING_BOOK_RED[] = {
    "WNFFDDDDAAAAAAAA",  // Ferzes and dabbabas grouped together
    "WNDDDDFFAAAAAAAA",  // Dabbabas first, then ferzes
    "WNAAFDDDDFAAAAAA"   // Pieces mixed for tactical play
};

const string OPENING_BOOK_BLUE[] = {
    "wnffddddaaaaaaaa",   // Ferzes and dabbabas grouped together
    "wnddddffaaaaaaaa",   // Dabbabas first, then ferzes
    "wnaafddddfaaaaaa"    // Pieces mixed for tactical play
};

// Move structure (defined before TTEntry)
struct Move {
    int r1, c1, r2, c2;
    char target;
    char piece;
    bool is_capture;
    bool is_revival;
    
    Move() : r1(0), c1(0), r2(0), c2(0), target('.'), piece('.'), is_capture(false), is_revival(false) {}
    
    Move(int r1, int c1, int r2, int c2, char target) 
        : r1(r1), c1(c1), r2(r2), c2(c2), target(target), piece('.'), is_capture(target != '.'), is_revival(false) {}
    
    Move(char piece, int r, int c) 
        : r1(0), c1(0), r2(r), c2(c), target('.'), piece(piece), is_capture(false), is_revival(true) {}
};

struct AttackMap {
    int red[8][8];
    int blue[8][8];
};

// Transposition Table Entry
struct TTEntry {
    uint64_t hash;
    int depth;
    int score;
    int flag; // 0 = exact, 1 = lower bound, 2 = upper bound
    Move best_move;
    bool valid;
    
    TTEntry() : hash(0), depth(-1), score(0), flag(0), best_move(), valid(false) {}
    
    TTEntry(const TTEntry& other) = default;
    TTEntry& operator=(const TTEntry& other) = default;
    TTEntry(TTEntry&& other) = default;
    TTEntry& operator=(TTEntry&& other) = default;
};

// Zobrist hashing for transposition table
uint64_t zobrist[8][8][12]; // 8x8 board, 12 piece types (6 pieces * 2 colors)
uint64_t zobrist_turn;

void init_zobrist() {
    mt19937_64 rng(12345); // Fixed seed for reproducibility
    for (int r = 0; r < 8; r++) {
        for (int c = 0; c < 8; c++) {
            for (int p = 0; p < 12; p++) {
                zobrist[r][c][p] = rng();
            }
        }
    }
    zobrist_turn = rng();
}

class ZeroPointOneAI {
private:
    char board[8][8];
    int capRed[5];
    int capBlue[5];
    bool isRed;
    bool ourTurn;
    chrono::steady_clock::time_point start_time;
    double time_limit;
    double total_time_used;
    int move_count;
    uint64_t current_hash;
    
    // Transposition table
    vector<TTEntry> transposition_table;
    Move killer_moves[20][2];
    int history[8][8][8][8];

    bool is_upper(char c) {
        return c >= 'A' && c <= 'Z';
    }
    
    bool is_lower(char c) {
        return c >= 'a' && c <= 'z';
    }
    
    int index_of(char c) {
        char u = toupper(c);
        switch(u) {
            case 'W': return 0;
            case 'N': return 1;
            case 'F': return 2;
            case 'D': return 3;
            case 'A': return 4;
            default: return -1;
        }
    }
    
    int get_piece_value(char piece) {
        if (piece == '.') return 0;
        int idx = index_of(piece);
        return idx >= 0 ? PIECE_VALUES[idx] : 0;
    }
    
    int piece_to_zobrist_index(char piece) {
        if (piece == '.') return -1;
        int base_idx = index_of(piece);
        if (base_idx < 0) return -1;
        return is_upper(piece) ? base_idx : base_idx + 6;
    }
    
    uint64_t compute_hash() {
        uint64_t hash = 0;
        for (int r = 0; r < 8; r++) {
            for (int c = 0; c < 8; c++) {
                int p_idx = piece_to_zobrist_index(board[r][c]);
                if (p_idx >= 0) {
                    hash ^= zobrist[r][c][p_idx];
                }
            }
        }
        if (!isRed) hash ^= zobrist_turn;
        return hash;
    }
    
    void update_hash_for_move(const Move& move) {
        if (move.is_revival) {
            int p_idx = piece_to_zobrist_index(move.piece);
            if (p_idx >= 0) {
                current_hash ^= zobrist[move.r2][move.c2][p_idx];
            }
        } else {
            int p_idx = piece_to_zobrist_index(board[move.r1][move.c1]);
            if (p_idx >= 0) {
                current_hash ^= zobrist[move.r1][move.c1][p_idx];
            }
            if (move.target != '.') {
                int t_idx = piece_to_zobrist_index(move.target);
                if (t_idx >= 0) {
                    current_hash ^= zobrist[move.r2][move.c2][t_idx];
                }
            }
            if (p_idx >= 0) {
                current_hash ^= zobrist[move.r2][move.c2][p_idx];
            }
        }
        current_hash ^= zobrist_turn;
    }

    TTEntry* probe_tt(uint64_t hash) {
        TTEntry& entry = transposition_table[hash & (TT_SIZE - 1)];
        if (entry.valid && entry.hash == hash) {
            return &entry;
        }
        return nullptr;
    }
    
    void store_tt(uint64_t hash, int depth, int score, int flag, const Move& best_move) {
        TTEntry& entry = transposition_table[hash & (TT_SIZE - 1)];
        entry.hash = hash;
        entry.depth = depth;
        entry.score = score;
        entry.flag = flag;
        entry.best_move = best_move;
        entry.valid = true;
    }

    int count_defenders(int r, int c, char piece) {
        int defenders = 0;
        bool ourIsRed = is_upper(piece);
        for (int sr = 0; sr < 8; sr++) {
            for (int sc = 0; sc < 8; sc++) {
                char sp = board[sr][sc];
                if (sp == '.') continue;
                if (ourIsRed && !is_upper(sp)) continue;
                if (!ourIsRed && !is_lower(sp)) continue;
                vector<Move> mvs = get_piece_moves(sr, sc, sp);
                for (const Move& mv : mvs) {
                    if (mv.r2 == r && mv.c2 == c) defenders++;
                }
            }
        }
        return defenders;
    }

    int piece_square_bonus(int r, int c, int idx, bool piece_is_red) {
        int forward = piece_is_red ? r : (7 - r);
        int center = 18 - int((abs(r - 3.5) + abs(c - 3.5)) * 4);
        int edge = min(min(r, 7 - r), min(c, 7 - c));
        int edge_bonus = edge * 4;
        switch (idx) {
            case 0: // Wazir
                return center * 3 + forward * 5 + edge_bonus * 2;
            case 1: // Knight
                return center * 4 + forward * 3 + edge_bonus * 2;
            case 2: // Ferz
                return center * 3 + forward * 4 + edge_bonus;
            case 3: // Dabbaba
                return center * 2 + forward * 5 + edge_bonus;
            case 4: // Alfil
                return center * 2 + forward * 6 + edge_bonus * 2;
            default:
                return center + forward * 2;
        }
    }

    int neighbor_support(int r, int c, bool piece_is_red) {
        int support = 0;
        for (int dr = -1; dr <= 1; dr++) {
            for (int dc = -1; dc <= 1; dc++) {
                if (dr == 0 && dc == 0) continue;
                int nr = r + dr, nc = c + dc;
                if (nr < 0 || nr >= 8 || nc < 0 || nc >= 8) continue;
                char neighbor = board[nr][nc];
                if (neighbor == '.') continue;
                if (piece_is_red == is_upper(neighbor)) support += 6;
            }
        }
        return support;
    }

    int evaluate_position(bool perspective_red, bool side_to_move_red) {
        int score = 0;
        int friendly_mobility = 0;
        int enemy_mobility = 0;
        
        for (int r = 0; r < 8; r++) {
            for (int c = 0; c < 8; c++) {
                char piece = board[r][c];
                if (piece == '.') continue;
                bool piece_is_red = is_upper(piece);
                int idx = index_of(piece);
                if (idx < 0) continue;
                
                int mobility = count_mobility(r, c, piece);
                int pst = piece_square_bonus(r, c, idx, piece_is_red);
                int support = neighbor_support(r, c, piece_is_red);
                int local_score = PIECE_VALUES[idx] + pst + support + mobility * MOBILITY_BONUS;
                
                if (piece_is_red == perspective_red) {
                    friendly_mobility += mobility;
                    score += local_score;
                    
                    if (idx == 0) {
                        int defenders = count_defenders(r, c, piece);
                        int king_bonus = defenders * 30;
                        if (is_under_attack(r, c, piece)) king_bonus -= KING_SAFETY_BONUS;
                        score += king_bonus;
                    }
                } else {
                    enemy_mobility += mobility;
                    score -= local_score;
                    
                    if (idx == 0) {
                        int defenders = count_defenders(r, c, piece);
                        int king_bonus = defenders * 30;
                        if (is_under_attack(r, c, piece)) king_bonus -= KING_SAFETY_BONUS;
                        score -= king_bonus;
                    }
                }
            }
        }
        
        score += (friendly_mobility - enemy_mobility) * MOBILITY_BONUS;
        
        // Captured pieces as revival potential
        int revival_bonus = 0;
        for (int i = 0; i < 5; i++) {
            int hold_value = REVIVAL_HOLDING_BONUS + PIECE_VALUES[i] / 12;
            int friendly_caps = perspective_red ? capRed[i] : capBlue[i];
            int enemy_caps = perspective_red ? capBlue[i] : capRed[i];
            revival_bonus += (friendly_caps - enemy_caps) * hold_value;
        }
        score += revival_bonus;
        
        score += evaluate_tactical_patterns(perspective_red);
        score += evaluate_endgame(perspective_red);
        
        if (side_to_move_red == perspective_red) score += TEMPO_BONUS;
        else score -= TEMPO_BONUS;
        
        return score;
    }

    int evaluate_board(bool side_to_move_red) {
        return evaluate_position(side_to_move_red, side_to_move_red);
    }

    vector<Move> get_piece_moves(int r, int c, char piece) {
        vector<Move> moves;
        char t = toupper(piece);
        auto add_move = [&](int nr, int nc) {
            if (nr >= 0 && nr < 8 && nc >= 0 && nc < 8) {
                Move mv(r, c, nr, nc, board[nr][nc]);
                mv.piece = piece;
                moves.push_back(mv);
            }
        };
        
        if (t == 'W') {
            for (int i = 0; i < 4; i++) {
                int nr = r + drW[i];
                int nc = c + dcW[i];
                add_move(nr, nc);
            }
        } else if (t == 'N') {
            for (int i = 0; i < 8; i++) {
                int nr = r + drN[i];
                int nc = c + dcN[i];
                add_move(nr, nc);
            }
        } else if (t == 'F') {
            for (int i = 0; i < 4; i++) {
                int nr = r + drF[i];
                int nc = c + dcF[i];
                add_move(nr, nc);
            }
        } else if (t == 'D') {
            for (int i = 0; i < 4; i++) {
                int nr = r + drD[i];
                int nc = c + dcD[i];
                add_move(nr, nc);
            }
        } else if (t == 'A') {
            for (int i = 0; i < 4; i++) {
                int nr = r + drA[i];
                int nc = c + dcA[i];
                add_move(nr, nc);
            }
        }
        
        return moves;
    }
    
    bool is_valid_move(const Move& move, bool is_red_turn) {
        if (move.is_revival) {
            if (board[move.r2][move.c2] != '.') return false;
            
            int idx = index_of(move.piece);
            if (idx == -1) return false;
            
            int* captured = is_red_turn ? capRed : capBlue;
            if (captured[idx] <= 0) return false;
            
            return true;
        } else {
            char piece = board[move.r1][move.c1];
            if (piece == '.') return false;
            
            if (is_red_turn && !is_upper(piece)) return false;
            if (!is_red_turn && !is_lower(piece)) return false;
            
            if (move.target != '.') {
                if ((is_red_turn && is_upper(move.target)) || 
                    (!is_red_turn && is_lower(move.target))) {
                    return false;
                }
            }
            
            return true;
        }
    }
    
    bool make_move(const Move& move, bool mover_is_red) {
        update_hash_for_move(move);
        
        if (move.is_revival) {
            board[move.r2][move.c2] = move.piece;
            int idx = index_of(move.piece);
            if (idx >= 0) {
                if (mover_is_red) capRed[idx]--;
                else capBlue[idx]--;
            }
            return false;
        } else {
            char piece = board[move.r1][move.c1];
            board[move.r2][move.c2] = piece;
            board[move.r1][move.c1] = '.';
            
            if (move.target != '.') {
                int idx = index_of(move.target);
                if (idx >= 0) {
                    if (mover_is_red) capRed[idx]++;
                    else capBlue[idx]++;
                }
                
                return toupper(move.target) == 'W';
            }
        }
        return false;
    }
    
    void unmake_move(const Move& move, bool mover_is_red) {
        if (move.is_revival) {
            board[move.r2][move.c2] = '.';
            int idx = index_of(move.piece);
            if (idx >= 0) {
                if (mover_is_red) capRed[idx]++;
                else capBlue[idx]++;
            }
        } else {
            char piece = board[move.r2][move.c2];
            board[move.r1][move.c1] = piece;
            board[move.r2][move.c2] = move.target;
            
            if (move.target != '.') {
                int idx = index_of(move.target);
                if (idx >= 0) {
                    if (mover_is_red) capRed[idx]--;
                    else capBlue[idx]--;
                }
            }
        }
        
        update_hash_for_move(move); // Undo the hash
    }
    
    vector<Move> get_all_moves(bool is_red_turn) {
        vector<Move> moves;
        
        // Regular moves
        for (int r = 0; r < 8; r++) {
            for (int c = 0; c < 8; c++) {
                char piece = board[r][c];
                if (piece == '.') continue;
                
                if (is_red_turn && !is_upper(piece)) continue;
                if (!is_red_turn && !is_lower(piece)) continue;
                
                vector<Move> piece_moves = get_piece_moves(r, c, piece);
                for (const Move& move : piece_moves) {
                    if (is_valid_move(move, is_red_turn)) {
                        moves.push_back(move);
                    }
                }
            }
        }
        
        // Revival moves - limit to avoid excessive computation
        int* captured = is_red_turn ? capRed : capBlue;
        int revival_count = 0;
        for (int i = 0; i < 5 && revival_count < 10; i++) { // Limit revival moves
            if (captured[i] > 0) {
                char piece;
                if (is_red_turn) {
                    char pieces[] = {'W', 'N', 'F', 'D', 'A'};
                    piece = pieces[i];
                } else {
                    char pieces[] = {'w', 'n', 'f', 'd', 'a'};
                    piece = pieces[i];
                }
                
                // Only check strategic positions for revival
                vector<pair<int,int>> strategic_positions = {
                    {3,3}, {3,4}, {4,3}, {4,4}, // Center
                    {2,2}, {2,5}, {5,2}, {5,5}, // Near center
                    {1,3}, {1,4}, {6,3}, {6,4}  // Development squares
                };
                
                for (auto pos : strategic_positions) {
                    if (board[pos.first][pos.second] == '.') {
                        Move revival_move(piece, pos.first, pos.second);
                        if (is_valid_move(revival_move, is_red_turn)) {
                            moves.push_back(revival_move);
                            revival_count++;
                            if (revival_count >= 10) break;
                        }
                    }
                }
            }
        }
        
        return moves;
    }

    void compute_attack_map(AttackMap& map) {
        memset(map.red, 0, sizeof(map.red));
        memset(map.blue, 0, sizeof(map.blue));
        for (int r = 0; r < 8; r++) {
            for (int c = 0; c < 8; c++) {
                char piece = board[r][c];
                if (piece == '.') continue;
                bool piece_is_red = is_upper(piece);
                vector<Move> moves = get_piece_moves(r, c, piece);
                for (const Move& mv : moves) {
                    if (piece_is_red) map.red[mv.r2][mv.c2]++;
                    else map.blue[mv.r2][mv.c2]++;
                }
            }
        }
    }
    
    int count_mobility(int r, int c, char piece) {
        vector<Move> moves = get_piece_moves(r, c, piece);
        return moves.size();
    }
    
    bool is_double_attack(int r, int c, char piece) {
        vector<Move> moves = get_piece_moves(r, c, piece);
        int enemy_targets = 0;
        bool piece_is_red = is_upper(piece);
        
        for (const Move& move : moves) {
            if (move.target == '.') continue;
            if ((piece_is_red && is_lower(move.target)) || (!piece_is_red && is_upper(move.target))) {
                enemy_targets++;
            }
        }
        
        return enemy_targets >= 2;
    }
    
    int evaluate_endgame(bool perspective_red) {
        int score = 0;
        int red_pieces = 0;
        int blue_pieces = 0;
        
        for (int r = 0; r < 8; r++) {
            for (int c = 0; c < 8; c++) {
                if (board[r][c] != '.') {
                    if (is_upper(board[r][c])) red_pieces++;
                    else blue_pieces++;
                }
            }
        }
        
        int total_pieces = red_pieces + blue_pieces;
        if (total_pieces <= 8) {
            for (int r = 0; r < 8; r++) {
                for (int c = 0; c < 8; c++) {
                    char piece = board[r][c];
                    if (toupper(piece) != 'W') continue;
                    double center_distance = abs(r - 3.5) + abs(c - 3.5);
                    int king_bonus = max(0, 100 - (int)(center_distance * 20));
                    bool friendly = (is_upper(piece) == perspective_red);
                    score += friendly ? king_bonus : -king_bonus;
                }
            }
        }
        
        return score;
    }
    
    int evaluate_tactical_patterns(bool perspective_red) {
        int score = 0;
        for (int r = 0; r < 8; r++) {
            for (int c = 0; c < 8; c++) {
                char piece = board[r][c];
                if (piece == '.') continue;
                if (!is_double_attack(r, c, piece)) continue;
                int piece_value = get_piece_value(piece) / 2;
                bool friendly = (is_upper(piece) == perspective_red);
                score += friendly ? piece_value : -piece_value;
            }
        }
        return score;
    }

    // Generate attack moves only (no revivals) for the given side
    vector<Move> get_attack_moves_for_side(bool sideIsRed) {
        vector<Move> attacks;
        for (int r = 0; r < 8; r++) {
            for (int c = 0; c < 8; c++) {
                char p = board[r][c];
                if (p == '.') continue;
                if (sideIsRed && !is_upper(p)) continue;
                if (!sideIsRed && !is_lower(p)) continue;
                vector<Move> mvs = get_piece_moves(r, c, p);
                for (const Move& mv : mvs) {
                    if (mv.target != '.') attacks.push_back(mv);
                }
            }
        }
        return attacks;
    }

    bool is_under_attack(int r, int c, char piece) {
        // Determine attacking side: opposite color of piece
        bool pieceIsRed = is_upper(piece);
        bool attackerIsRed = !pieceIsRed;

        for (int sr = 0; sr < 8; sr++) {
            for (int sc = 0; sc < 8; sc++) {
                char sp = board[sr][sc];
                if (sp == '.') continue;
                if (attackerIsRed && !is_upper(sp)) continue;
                if (!attackerIsRed && !is_lower(sp)) continue;
                vector<Move> mvs = get_piece_moves(sr, sc, sp);
                for (const Move& mv : mvs) {
                    if (mv.r2 == r && mv.c2 == c && mv.target != '.') return true;
                }
            }
        }
        return false;
    }

    
    void order_moves(vector<Move>& moves, bool is_red_turn, int ply, Move* tt_move = nullptr) {
        sort(moves.begin(), moves.end(), [this, is_red_turn, ply, tt_move](const Move& a, const Move& b) {
            int score_a = 0, score_b = 0;
            
            // Highest priority: TT (hash) move
            if (tt_move != nullptr) {
                if (!a.is_revival && !tt_move->is_revival && 
                    a.r1 == tt_move->r1 && a.c1 == tt_move->c1 && 
                    a.r2 == tt_move->r2 && a.c2 == tt_move->c2) {
                    score_a = 30000;
                }
                if (!b.is_revival && !tt_move->is_revival && 
                    b.r1 == tt_move->r1 && b.c1 == tt_move->c1 && 
                    b.r2 == tt_move->r2 && b.c2 == tt_move->c2) {
                    score_b = 30000;
                }
            }
            
            // King capture
            if (a.is_capture && toupper(a.target) == 'W') {
                score_a = 20000;
            }
            if (b.is_capture && toupper(b.target) == 'W') {
                score_b = 20000;
            }
            
            // MVV-LVA for other captures
            if (a.is_capture && toupper(a.target) != 'W') {
                score_a = 10000 + get_piece_value(a.target) * 10 - get_piece_value(board[a.r1][a.c1]);
            }
            if (b.is_capture && toupper(b.target) != 'W') {
                score_b = 10000 + get_piece_value(b.target) * 10 - get_piece_value(board[b.r1][b.c1]);
            }
            
            // Killer moves
            if (!a.is_revival && !a.is_capture && ply < 20) {
                if ((a.r1 == killer_moves[ply][0].r1 && a.c1 == killer_moves[ply][0].c1 && 
                     a.r2 == killer_moves[ply][0].r2 && a.c2 == killer_moves[ply][0].c2) ||
                    (a.r1 == killer_moves[ply][1].r1 && a.c1 == killer_moves[ply][1].c1 && 
                     a.r2 == killer_moves[ply][1].r2 && a.c2 == killer_moves[ply][1].c2)) {
                    score_a += 5000;
                }
            }
            if (!b.is_revival && !b.is_capture && ply < 20) {
                if ((b.r1 == killer_moves[ply][0].r1 && b.c1 == killer_moves[ply][0].c1 && 
                     b.r2 == killer_moves[ply][0].r2 && b.c2 == killer_moves[ply][0].c2) ||
                    (b.r1 == killer_moves[ply][1].r1 && b.c1 == killer_moves[ply][1].c1 && 
                     b.r2 == killer_moves[ply][1].r2 && b.c2 == killer_moves[ply][1].c2)) {
                    score_b += 5000;
                }
            }
            
            // History heuristic
            if (!a.is_revival) {
                score_a += history[a.r1][a.c1][a.r2][a.c2];
            }
            if (!b.is_revival) {
                score_b += history[b.r1][b.c1][b.r2][b.c2];
            }
            
            // Positional bonuses
            if (is_red_turn) {
                score_a += a.r2 * 10;
                score_b += b.r2 * 10;
            } else {
                score_a += (7 - a.r2) * 10;
                score_b += (7 - b.r2) * 10;
            }
            
            // Center control
            double center_a = abs(a.r2 - 3.5) + abs(a.c2 - 3.5);
            double center_b = abs(b.r2 - 3.5) + abs(b.c2 - 3.5);
            score_a += 50 - (int)(center_a * 10);
            score_b += 50 - (int)(center_b * 10);
            
            return score_a > score_b;
        });
    }
    
    int quiescence(int alpha, int beta, bool is_red_turn) {
        // Stand-pat evaluation
    int stand_pat = evaluate_board(is_red_turn);
        if (stand_pat >= beta) return stand_pat;
        if (stand_pat > alpha) alpha = stand_pat;
        
        // Generate capture moves only
        vector<Move> capture_moves;
        vector<Move> all_moves = get_all_moves(is_red_turn);
        
        for (const Move& mv : all_moves) {
            if (mv.is_capture && mv.target != '.') {
                capture_moves.push_back(mv);
            }
        }
        
        // Order captures by MVV-LVA
        sort(capture_moves.begin(), capture_moves.end(), 
             [this](const Move& a, const Move& b) {
                 return get_piece_value(a.target) - get_piece_value(board[a.r1][a.c1]) >
                        get_piece_value(b.target) - get_piece_value(board[b.r1][b.c1]);
             });
        
        for (const Move& mv : capture_moves) {
            auto current_time = chrono::steady_clock::now();
            double elapsed = chrono::duration<double>(current_time - start_time).count();
            if (elapsed > time_limit * 0.6) break; // Much stricter limit for quiescence
            
            make_move(mv, is_red_turn);
            int score = -quiescence(-beta, -alpha, !is_red_turn);
            unmake_move(mv, is_red_turn);
            
            if (score >= beta) return score;
            if (score > alpha) alpha = score;
        }
        
        return alpha;
    }
    
    int negamax(int depth, int alpha, int beta, bool is_red_turn, int ply) {
        // Time check
        auto current_time = chrono::steady_clock::now();
        double elapsed = chrono::duration<double>(current_time - start_time).count();
        if (elapsed > time_limit * 0.85) {
            return evaluate_board(is_red_turn);
        }
        
        // Check transposition table
        Move* tt_move = nullptr;
        if (TTEntry* tt_entry = probe_tt(current_hash)) {
            if (tt_entry->depth >= depth) {
                if (tt_entry->flag == 0) { // Exact score
                    return tt_entry->score;
                } else if (tt_entry->flag == 1) { // Lower bound
                    alpha = max(alpha, tt_entry->score);
                } else if (tt_entry->flag == 2) { // Upper bound
                    beta = min(beta, tt_entry->score);
                }
                if (alpha >= beta) {
                    return tt_entry->score;
                }
            }
            tt_move = &tt_entry->best_move;
        }
        
        if (depth <= 0) {
            return quiescence(alpha, beta, is_red_turn);
        }
        
        vector<Move> moves = get_all_moves(is_red_turn);
        if (moves.empty()) {
            return evaluate_board(is_red_turn);
        }
        
        order_moves(moves, is_red_turn, ply, tt_move);
        
        // Adaptive move pruning based on depth
        int max_moves = 30;
        if (depth >= 4) max_moves = 10;
        else if (depth >= 3) max_moves = 15;
        else if (depth >= 2) max_moves = 20;
        
        if (moves.size() > (size_t)max_moves) {
            moves.resize(max_moves);
        }
        
        int best_score = INT_MIN;
        Move best_move;
        int original_alpha = alpha;
        
        for (size_t i = 0; i < moves.size(); i++) {
            const Move& move = moves[i];
            if (!is_valid_move(move, is_red_turn)) continue;
            
            // Time check for deep searches
            if (i > 5 && depth >= 2) {
                auto current_time = chrono::steady_clock::now();
                double elapsed = chrono::duration<double>(current_time - start_time).count();
                if (elapsed > time_limit * 0.7) break;
            }
            
            bool won = make_move(move, is_red_turn);
            if (won) {
                unmake_move(move, is_red_turn);
                int win_score = 100000 - ply;
                
                // Store in TT
                store_tt(current_hash, depth, win_score, 0, move);
                
                return win_score;
            }
            
            int score;
            // Light Multi-Join Reduction (LMR) for quiet late moves
            if (depth >= 3 && i > 3 && !move.is_capture && !move.is_revival) {
                // reduced search first
                score = -negamax(depth - 2, -alpha - 1, -alpha, !is_red_turn, ply + 1);
                if (score > alpha) {
                    // if promising, do full search
                    score = -negamax(depth - 1, -beta, -alpha, !is_red_turn, ply + 1);
                }
            } else {
                score = -negamax(depth - 1, -beta, -alpha, !is_red_turn, ply + 1);
            }
            unmake_move(move, is_red_turn);
            
            if (score > best_score) {
                best_score = score;
                best_move = move;
            }
            
            alpha = max(alpha, score);
            if (alpha >= beta) {
                // Beta cutoff - store killer move and update history
                if (!move.is_revival && !move.is_capture && ply < 20) {
                    if (killer_moves[ply][0].r1 != move.r1 || killer_moves[ply][0].c1 != move.c1 ||
                        killer_moves[ply][0].r2 != move.r2 || killer_moves[ply][0].c2 != move.c2) {
                        killer_moves[ply][1] = killer_moves[ply][0];
                        killer_moves[ply][0] = move;
                    }
                }
                if (!move.is_revival) {
                    history[move.r1][move.c1][move.r2][move.c2] += depth * depth;
                }
                break;
            }
        }
        
        // Store in transposition table
        int flag = 0;
        if (best_score <= original_alpha) {
            flag = 2; // Upper bound
        } else if (best_score >= beta) {
            flag = 1; // Lower bound
        }
        store_tt(current_hash, depth, best_score, flag, best_move);
        
        return best_score;
    }
    
    Move get_best_move() {
        vector<Move> moves = get_all_moves(isRed);
        if (moves.empty()) {
            return Move();
        }
        
        // Check for immediate wins
        for (const Move& move : moves) {
            bool won = make_move(move, isRed);
            if (won) {
                unmake_move(move, isRed);
                return move;
            }
            unmake_move(move, isRed);
        }
        
        // Iterative deepening
        Move best_move;
        int best_score = INT_MIN;
        
        for (int depth = 1; depth <= 20; depth++) {
            auto current_time = chrono::steady_clock::now();
            double elapsed = chrono::duration<double>(current_time - start_time).count();
            
            // Stop if we're running out of time
            if (elapsed > time_limit * 0.8) {
                break;
            }
            
            // Estimate if we have time for next depth
            if (depth > 3 && elapsed > time_limit * 0.5) {
                break;
            }
            
            int depth_best_score = INT_MIN;
            Move depth_best_move;
            
            // Get TT move if available
            Move* tt_move = nullptr;
            if (TTEntry* tt_entry = probe_tt(current_hash)) {
                tt_move = &tt_entry->best_move;
            }
            
            order_moves(moves, isRed, 0, tt_move);
            
            bool completed_depth = false;
            for (const Move& move : moves) {
                if (!is_valid_move(move, isRed)) continue;
                
                current_time = chrono::steady_clock::now();
                elapsed = chrono::duration<double>(current_time - start_time).count();
                if (elapsed > time_limit * 0.85) {
                    break;
                }
                
                bool won = make_move(move, isRed);
                if (won) {
                    unmake_move(move, isRed);
                    return move;
                }
                
                int score = -negamax(depth - 1, INT_MIN, INT_MAX, !isRed, 1);
                unmake_move(move, isRed);
                
                if (score > depth_best_score) {
                    depth_best_score = score;
                    depth_best_move = move;
                    completed_depth = true;
                }
            }
            
            // Only update best move if we completed this depth
            if (completed_depth) {
                best_move = depth_best_move;
                best_score = depth_best_score;
            } else {
                // Didn't complete this depth, stop searching
                break;
            }
            
            // If we found a winning move, stop searching
            if (best_score > 50000) {
                break;
            }
        }
        
        // Fallback if no move was found
        if (best_move.piece == '\0' && !best_move.is_revival && 
            best_move.r1 == 0 && best_move.c1 == 0 && best_move.r2 == 0 && best_move.c2 == 0) {
            for (const Move& move : moves) {
                if (is_valid_move(move, isRed)) {
                    return move;
                }
            }
            if (!moves.empty()) {
                return moves[0];
            }
        }
        
        return best_move;
    }
    
    string get_opening_sequence(const string& color) {
        mt19937 rng(chrono::steady_clock::now().time_since_epoch().count());
        int idx = rng() % 3;
        
        if (color == "red") {
            return OPENING_BOOK_RED[idx];
        } else {
            return OPENING_BOOK_BLUE[idx];
        }
    }
    
    string format_move(const Move& move) {
        if (move.is_revival) {
            return string(1, move.piece) + char('a' + move.r2) + to_string(move.c2 + 1);
        } else {
            return string(1, char('a' + move.r1)) + to_string(move.c1 + 1) + 
                   char('a' + move.r2) + to_string(move.c2 + 1);
        }
    }
    
public:
    ZeroPointOneAI() : isRed(false), ourTurn(false), time_limit(30.0), total_time_used(0.0), move_count(0), current_hash(0), transposition_table(TT_SIZE) {
        // Initialize Zobrist hashing
        init_zobrist();
        
        // Initialize board
        for (int i = 0; i < 8; i++) {
            for (int j = 0; j < 8; j++) {
                board[i][j] = '.';
            }
        }
        
        // Initialize captured pieces
        for (int i = 0; i < 5; i++) {
            capRed[i] = 0;
            capBlue[i] = 0;
        }
        
        // Initialize killer moves
        for (int i = 0; i < 20; i++) {
            killer_moves[i][0] = Move();
            killer_moves[i][1] = Move();
        }
        
        // Initialize history heuristic
        for (int i = 0; i < 8; i++) {
            for (int j = 0; j < 8; j++) {
                for (int k = 0; k < 8; k++) {
                    for (int l = 0; l < 8; l++) {
                        history[i][j][k][l] = 0;
                    }
                }
            }
        }
    }
    
    void play_game() {
        string line;
        getline(cin, line);
        
        if (line.empty()) {
            exit(0);
        }
        
        if (line == "Start") {
            isRed = true;
            string seq = get_opening_sequence("red");
            cout << seq << endl;
            cout.flush();
            
            string oppseq;
            getline(cin, oppseq);
            
            // Set up board
            for (int i = 0; i < 8; i++) {
                board[0][i] = (i < (int)seq.length()) ? seq[i] : '.';
            }
            for (int i = 0; i < 8; i++) {
                board[1][i] = (8 + i < (int)seq.length()) ? seq[8 + i] : '.';
            }
            for (int i = 0; i < 8; i++) {
                board[6][i] = (i < (int)oppseq.length()) ? oppseq[i] : '.';
            }
            for (int i = 0; i < 8; i++) {
                board[7][i] = (8 + i < (int)oppseq.length()) ? oppseq[8 + i] : '.';
            }
            ourTurn = true;
        } else {
            isRed = false;
            string redseq = line;
            string seq = get_opening_sequence("blue");
            cout << seq << endl;
            cout.flush();
            
            // Set up board
            for (int i = 0; i < 8; i++) {
                board[0][i] = (i < (int)redseq.length()) ? redseq[i] : '.';
            }
            for (int i = 0; i < 8; i++) {
                board[1][i] = (8 + i < (int)redseq.length()) ? redseq[8 + i] : '.';
            }
            for (int i = 0; i < 8; i++) {
                board[6][i] = (i < (int)seq.length()) ? seq[i] : '.';
            }
            for (int i = 0; i < 8; i++) {
                board[7][i] = (8 + i < (int)seq.length()) ? seq[8 + i] : '.';
            }
            ourTurn = false;
        }
        
        // Initialize hash after board setup
        current_hash = compute_hash();
        
        while (true) {
            // Check for 102-move draw rule
            if (move_count >= 102) {
                break;
            }
            
            if (ourTurn) {
                start_time = chrono::steady_clock::now();
                
                // Adaptive time management
                double remaining_budget = max(0.0, 28.0 - total_time_used);
                int estimated_remaining_moves = max(5, (102 - move_count) / 2);
                double per_move_budget = min(3.0, remaining_budget / estimated_remaining_moves);
                per_move_budget = max(0.3, per_move_budget);
                time_limit = per_move_budget;
                
                Move best_move = get_best_move();
                
                auto end_time = chrono::steady_clock::now();
                double elapsed = chrono::duration<double>(end_time - start_time).count();
                total_time_used += elapsed;
                
                // Validate the move before sending - find fallback if invalid
                if (!is_valid_move(best_move, isRed) || 
                    (best_move.piece == '\0' && !best_move.is_revival && 
                     best_move.r1 == 0 && best_move.c1 == 0 && 
                     best_move.r2 == 0 && best_move.c2 == 0)) {
                    
                    // Find any valid move as fallback
                    vector<Move> all_moves = get_all_moves(isRed);
                    bool found_valid = false;
                    
                    for (const Move& move : all_moves) {
                        if (is_valid_move(move, isRed)) {
                            best_move = move;
                            found_valid = true;
                            break;
                        }
                    }
                    
                    // If still no valid move, try revival moves
                    if (!found_valid) {
                        for (const Move& move : all_moves) {
                            if (move.is_revival && is_valid_move(move, isRed)) {
                                best_move = move;
                                found_valid = true;
                                break;
                            }
                        }
                    }
                    
                    // Last resort - any move
                    if (!found_valid && !all_moves.empty()) {
                        best_move = all_moves[0];
                    }
                }
                
                string move_str = format_move(best_move);
                
                // Ensure we always output a valid move
                if (move_str.empty() || (move_str.length() != 4 && move_str.length() != 3)) {
                    // Generate a simple fallback move
                    vector<Move> all_moves = get_all_moves(isRed);
                    if (!all_moves.empty()) {
                        best_move = all_moves[0];
                        move_str = format_move(best_move);
                    }
                }
                
                cout << move_str << endl;
                cout.flush();
                
                bool won = make_move(best_move, isRed);
                move_count++;
                if (won) break;
                
                ourTurn = false;
            } else {
                getline(cin, line);
                if (line.empty()) break;
                
                if (line == "Quit") break;
                
                if (line.length() == 4) {
                    int r1 = line[0] - 'a';
                    int c1 = line[1] - '1';
                    int r2 = line[2] - 'a';
                    int c2 = line[3] - '1';
                    
                    char moving = board[r1][c1];
                    char dest = board[r2][c2];
                    
                    // Update hash for opponent move
                    Move opp_move(r1, c1, r2, c2, dest);
                    update_hash_for_move(opp_move);
                    
                    board[r2][c2] = moving;
                    board[r1][c1] = '.';
                    
                    if (dest != '.') {
                        int idx = index_of(dest);
                        // When opponent captures our piece, THEY get it
                        if (isRed) capBlue[idx]++;  // Opponent (Blue) captured our piece
                        else capRed[idx]++;         // Opponent (Red) captured our piece
                        
                        if ((isRed && dest == 'w') || (!isRed && dest == 'W')) {
                            break;
                        }
                    }
                    move_count++;
                } else if (line.length() == 3) {
                    char piece = line[0];
                    int r = line[1] - 'a';
                    int c = line[2] - '1';
                    
                    // Update hash for opponent revival
                    Move opp_move(piece, r, c);
                    update_hash_for_move(opp_move);
                    
                    board[r][c] = piece;
                    int idx = index_of(piece);
                    
                    // Opponent is reviving their piece from their captures
                    if ((isRed && is_lower(piece)) || (!isRed && is_upper(piece))) {
                        // Opponent (Blue if we're Red, Red if we're Blue) revives their piece
                        if (isRed) capBlue[idx]--;  // Blue uses their capture
                        else capRed[idx]--;         // Red uses their capture
                    } else {
                        // Shouldn't happen - opponent reviving our piece?
                        if (isRed) capRed[idx]--;
                        else capBlue[idx]--;
                    }
                    move_count++;
                }
                
                ourTurn = true;
            }
        }
    }
};

int main() {
    ZeroPointOneAI ai;
    ai.play_game();
    return 0;
}
// hello

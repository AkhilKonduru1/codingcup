#include <iostream>
#include <vector>
#include <string>
#include <algorithm>
#include <chrono>
#include <climits>
#include <cmath>
#include <unordered_map>
#include <random>

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
const int MOBILITY_BONUS = 5;

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

// Transposition Table Entry
struct TTEntry {
    uint64_t hash;
    int depth;
    int score;
    int flag; // 0 = exact, 1 = lower bound, 2 = upper bound
    Move best_move;
    
    TTEntry() : hash(0), depth(0), score(0), flag(0), best_move() {}
    
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
    
    // Transposition table
    unordered_map<uint64_t, TTEntry> transposition_table;
    uint64_t current_hash;
    
    // Killer moves (2 per ply, max depth 20)
    Move killer_moves[20][2];
    
    // History heuristic
    int history[8][8][8][8]; // [from_r][from_c][to_r][to_c]
    
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
        // Upper case (Red) = 0-5, Lower case (Blue) = 6-11
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
            // Remove piece from source
            int p_idx = piece_to_zobrist_index(board[move.r1][move.c1]);
            if (p_idx >= 0) {
                current_hash ^= zobrist[move.r1][move.c1][p_idx];
            }
            // Remove captured piece from destination
            if (move.target != '.') {
                int t_idx = piece_to_zobrist_index(move.target);
                if (t_idx >= 0) {
                    current_hash ^= zobrist[move.r2][move.c2][t_idx];
                }
            }
            // Add piece to destination
            if (p_idx >= 0) {
                current_hash ^= zobrist[move.r2][move.c2][p_idx];
            }
        }
        current_hash ^= zobrist_turn; // Toggle turn
    }
    
    vector<Move> get_piece_moves(int r, int c, char piece) {
        vector<Move> moves;
        char t = toupper(piece);
        
        if (t == 'W') {
            for (int i = 0; i < 4; i++) {
                int nr = r + drW[i];
                int nc = c + dcW[i];
                if (nr >= 0 && nr < 8 && nc >= 0 && nc < 8) {
                    moves.push_back(Move(r, c, nr, nc, board[nr][nc]));
                }
            }
        } else if (t == 'N') {
            for (int i = 0; i < 8; i++) {
                int nr = r + drN[i];
                int nc = c + dcN[i];
                if (nr >= 0 && nr < 8 && nc >= 0 && nc < 8) {
                    moves.push_back(Move(r, c, nr, nc, board[nr][nc]));
                }
            }
        } else if (t == 'F') {
            for (int i = 0; i < 4; i++) {
                int nr = r + drF[i];
                int nc = c + dcF[i];
                if (nr >= 0 && nr < 8 && nc >= 0 && nc < 8) {
                    moves.push_back(Move(r, c, nr, nc, board[nr][nc]));
                }
            }
        } else if (t == 'D') {
            for (int i = 0; i < 4; i++) {
                int nr = r + drD[i];
                int nc = c + dcD[i];
                if (nr >= 0 && nr < 8 && nc >= 0 && nc < 8) {
                    moves.push_back(Move(r, c, nr, nc, board[nr][nc]));
                }
            }
        } else if (t == 'A') {
            for (int i = 0; i < 4; i++) {
                int nr = r + drA[i];
                int nc = c + dcA[i];
                if (nr >= 0 && nr < 8 && nc >= 0 && nc < 8) {
                    moves.push_back(Move(r, c, nr, nc, board[nr][nc]));
                }
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
    
    bool make_move(const Move& move, bool red_turn) {
        update_hash_for_move(move);

        if (move.is_revival) {
            board[move.r2][move.c2] = move.piece;
            int idx = index_of(move.piece);
            if (idx >= 0) {
                if (red_turn) capRed[idx]--;
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
                    if (red_turn) capRed[idx]++;
                    else capBlue[idx]++;
                }

                return toupper(move.target) == 'W';
            }
        }
        return false;
    }

    void unmake_move(const Move& move, bool red_turn) {
        if (move.is_revival) {
            board[move.r2][move.c2] = '.';
            int idx = index_of(move.piece);
            if (idx >= 0) {
                if (red_turn) capRed[idx]++;
                else capBlue[idx]++;
            }
        } else {
            char piece = board[move.r2][move.c2];
            board[move.r1][move.c1] = piece;
            board[move.r2][move.c2] = move.target;

            if (move.target != '.') {
                int idx = index_of(move.target);
                if (idx >= 0) {
                    if (red_turn) capRed[idx]--;
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
    
    void compute_attack_maps(int attack_red[8][8], int attack_blue[8][8],
                             int& mobility_red, int& mobility_blue, int& tactical_score) {
        for (int r = 0; r < 8; r++) {
            for (int c = 0; c < 8; c++) {
                char piece = board[r][c];
                if (piece == '.') continue;

                bool red_piece = is_upper(piece);
                bool our_piece = (isRed && red_piece) || (!isRed && !red_piece);

                vector<Move> moves = get_piece_moves(r, c, piece);
                int enemy_targets = 0;

                for (const Move& move : moves) {
                    if (red_piece) attack_red[move.r2][move.c2]++;
                    else attack_blue[move.r2][move.c2]++;

                    char target = board[move.r2][move.c2];
                    bool friendly_target = (red_piece && is_upper(target)) ||
                                           (!red_piece && is_lower(target));

                    if (!friendly_target) {
                        if (red_piece) mobility_red++;
                        else mobility_blue++;

                        if (target != '.' &&
                            ((red_piece && is_lower(target)) ||
                             (!red_piece && is_upper(target)))) {
                            enemy_targets++;
                        }
                    }
                }

                if (enemy_targets >= 2) {
                    int piece_value = get_piece_value(piece);
                    tactical_score += our_piece ? piece_value / 2 : -piece_value / 2;
                }
            }
        }
    }

    bool find_king_position(bool red_king, int& out_r, int& out_c) {
        out_r = -1;
        out_c = -1;
        char target = red_king ? 'W' : 'w';
        for (int r = 0; r < 8; r++) {
            for (int c = 0; c < 8; c++) {
                if (board[r][c] == target) {
                    out_r = r;
                    out_c = c;
                    return true;
                }
            }
        }
        return false;
    }

    int count_attackers_on_square(int r, int c, bool attackers_are_red) {
        if (r < 0 || r >= 8 || c < 0 || c >= 8) return 0;

        int count = 0;
        auto consider = [&](int sr, int sc, char piece_type) {
            if (sr < 0 || sr >= 8 || sc < 0 || sc >= 8) return;
            char piece = board[sr][sc];
            if (piece == '.') return;
            if (attackers_are_red) {
                if (!is_upper(piece)) return;
            } else {
                if (!is_lower(piece)) return;
            }
            if (toupper(piece) == piece_type) {
                count++;
            }
        };

        for (int i = 0; i < 4; i++) {
            consider(r - drW[i], c - dcW[i], 'W');
        }
        for (int i = 0; i < 8; i++) {
            consider(r - drN[i], c - dcN[i], 'N');
        }
        for (int i = 0; i < 4; i++) {
            consider(r - drF[i], c - dcF[i], 'F');
        }
        for (int i = 0; i < 4; i++) {
            consider(r - drD[i], c - dcD[i], 'D');
        }
        for (int i = 0; i < 4; i++) {
            consider(r - drA[i], c - dcA[i], 'A');
        }

        return count;
    }

    bool is_in_check(bool red_turn) {
        int kr = -1, kc = -1;
        if (!find_king_position(red_turn, kr, kc)) {
            return false;
        }
        return count_attackers_on_square(kr, kc, !red_turn) > 0;
    }

    int evaluate_endgame() {
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
                    if (toupper(piece) == 'W') {
                        if ((isRed && is_upper(piece)) || (!isRed && is_lower(piece))) {
                            double center_distance = abs(r - 3.5) + abs(c - 3.5);
                            score += max(0, 100 - (int)(center_distance * 20));
                        }
                    }
                }
            }
        }
        
        return score;
    }

    int evaluate_board() {
        int attack_red[8][8] = {};
        int attack_blue[8][8] = {};
        int mobility_red = 0;
        int mobility_blue = 0;
        int tactical_score = 0;

        compute_attack_maps(attack_red, attack_blue, mobility_red, mobility_blue, tactical_score);

        int red_king_r, red_king_c, blue_king_r, blue_king_c;
        find_king_position(true, red_king_r, red_king_c);
        find_king_position(false, blue_king_r, blue_king_c);

        int score = tactical_score;

        int our_mobility = isRed ? mobility_red : mobility_blue;
        int opp_mobility = isRed ? mobility_blue : mobility_red;

        for (int r = 0; r < 8; r++) {
            for (int c = 0; c < 8; c++) {
                char piece = board[r][c];
                if (piece == '.') continue;

                int piece_value = get_piece_value(piece);
                bool red_piece = is_upper(piece);
                bool our_piece = (isRed && red_piece) || (!isRed && !red_piece);

                double center_distance = abs(r - 3.5) + abs(c - 3.5);
                int center_bonus = max(0, 40 - (int)(center_distance * 4));

                int coordination_bonus = 0;
                for (int dr = -1; dr <= 1; dr++) {
                    for (int dc = -1; dc <= 1; dc++) {
                        if (dr == 0 && dc == 0) continue;
                        int nr = r + dr, nc = c + dc;
                        if (nr >= 0 && nr < 8 && nc >= 0 && nc < 8) {
                            char neighbor = board[nr][nc];
                            if (neighbor != '.' &&
                                ((is_upper(piece) && is_upper(neighbor)) ||
                                 (is_lower(piece) && is_lower(neighbor)))) {
                                coordination_bonus += 12;
                            }
                        }
                    }
                }

                if (our_piece) {
                    score += piece_value + center_bonus + coordination_bonus;

                    int advancement_bonus = 0;
                    if (isRed && r >= 4) advancement_bonus = (r - 3) * 25;
                    else if (!isRed && r <= 3) advancement_bonus = (4 - r) * 25;
                    score += advancement_bonus;

                    if ((r == 3 || r == 4) && (c == 3 || c == 4)) {
                        score += 60;
                    }

                    int defenders = red_piece ? attack_red[r][c] : attack_blue[r][c];
                    score += defenders * 8;

                    if (toupper(piece) == 'W') {
                        bool under_attack = red_piece ? (attack_blue[r][c] > 0)
                                                      : (attack_red[r][c] > 0);
                        score += defenders * 35;
                        if (under_attack) {
                            score -= 150;
                        }
                    }
                } else {
                    score -= piece_value + center_bonus;

                    if (toupper(piece) == 'W') {
                        bool under_attack = red_piece ? (attack_blue[r][c] > 0)
                                                      : (attack_red[r][c] > 0);
                        if (under_attack) {
                            score += 120;
                        }
                    }
                }
            }
        }

        score += (our_mobility - opp_mobility) * MOBILITY_BONUS;

        for (int i = 0; i < 5; i++) {
            int piece_value = PIECE_VALUES[i];
            if (isRed) {
                score += capRed[i] * piece_value;
                score -= capBlue[i] * piece_value;
            } else {
                score += capBlue[i] * piece_value;
                score -= capRed[i] * piece_value;
            }
        }

        int red_king_attackers = red_king_r >= 0 ? count_attackers_on_square(red_king_r, red_king_c, false) : 0;
        int blue_king_attackers = blue_king_r >= 0 ? count_attackers_on_square(blue_king_r, blue_king_c, true) : 0;

        int our_king_attackers = isRed ? red_king_attackers : blue_king_attackers;
        int opp_king_attackers = isRed ? blue_king_attackers : red_king_attackers;

        if (our_king_attackers > 0) {
            score -= 800 + 220 * (our_king_attackers - 1);
        }
        if (opp_king_attackers > 0) {
            score += 800 + 200 * (opp_king_attackers - 1);
        }

        score += evaluate_endgame();

        return score;
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
        int stand_pat = evaluate_board();
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
            return evaluate_board() * (is_red_turn == isRed ? 1 : -1);
        }

        bool in_check = is_in_check(is_red_turn);
        int extension_current = (in_check && depth > 0) ? 1 : 0;
        int search_depth = depth + extension_current;

        // Check transposition table
        TTEntry* tt_entry = nullptr;
        Move* tt_move = nullptr;
        if (transposition_table.count(current_hash)) {
            tt_entry = &transposition_table[current_hash];
            if (tt_entry->depth >= search_depth) {
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

        if (search_depth <= 0) {
            return quiescence(alpha, beta, is_red_turn);
        }

        vector<Move> moves = get_all_moves(is_red_turn);
        if (moves.empty()) {
            if (in_check) {
                return (is_red_turn == isRed) ? (-100000 + ply) : (100000 - ply);
            }
            return evaluate_board() * (is_red_turn == isRed ? 1 : -1);
        }

        order_moves(moves, is_red_turn, ply, tt_move);

        // Adaptive move pruning based on depth
        if (!in_check) {
            int max_moves = 30;
            if (search_depth >= 4) max_moves = 10;
            else if (search_depth >= 3) max_moves = 15;
            else if (search_depth >= 2) max_moves = 20;

            if (moves.size() > (size_t)max_moves) {
                moves.resize(max_moves);
            }
        }

        int best_score = INT_MIN;
        Move best_move;
        int original_alpha = alpha;

        for (size_t i = 0; i < moves.size(); i++) {
            const Move& move = moves[i];
            if (!is_valid_move(move, is_red_turn)) continue;

            // Time check for deep searches
            if (i > 5 && search_depth >= 2) {
                auto current_time = chrono::steady_clock::now();
                double elapsed = chrono::duration<double>(current_time - start_time).count();
                if (elapsed > time_limit * 0.7) break;
            }

            bool won = make_move(move, is_red_turn);
            if (won) {
                unmake_move(move, is_red_turn);
                int win_score = 100000 - ply;

                // Store in TT
                TTEntry entry;
                entry.hash = current_hash;
                entry.depth = search_depth;
                entry.score = win_score;
                entry.flag = 0;
                entry.best_move = move;
                transposition_table[current_hash] = entry;

                return win_score;
            }

            bool opponent_in_check = is_in_check(!is_red_turn);
            int next_depth = search_depth - 1;
            if (opponent_in_check && next_depth > 0) {
                next_depth++;
            }

            int score = -negamax(next_depth, -beta, -alpha, !is_red_turn, ply + 1);
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
                    history[move.r1][move.c1][move.r2][move.c2] += search_depth * search_depth;
                }
                break;
            }
        }

        // Store in transposition table
        TTEntry entry;
        entry.hash = current_hash;
        entry.depth = search_depth;
        entry.score = best_score;
        if (best_score <= original_alpha) {
            entry.flag = 2; // Upper bound
        } else if (best_score >= beta) {
            entry.flag = 1; // Lower bound
        } else {
            entry.flag = 0; // Exact
        }
        entry.best_move = best_move;
        transposition_table[current_hash] = entry;
        
        return best_score;
    }
    
    bool has_critical_threat() {
        int kr, kc;
        if (!find_king_position(isRed, kr, kc)) {
            return true;
        }
        return count_attackers_on_square(kr, kc, !isRed) > 0;
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

        bool urgent = has_critical_threat();

        for (int depth = 1; depth <= 20; depth++) {
            auto current_time = chrono::steady_clock::now();
            double elapsed = chrono::duration<double>(current_time - start_time).count();

            // Stop if we're running out of time
            double soft_cap = urgent ? 0.9 : 0.8;
            if (elapsed > time_limit * soft_cap) {
                break;
            }

            // Estimate if we have time for next depth
            if (!urgent && depth > 3 && elapsed > time_limit * 0.5) {
                break;
            }

            int depth_best_score = INT_MIN;
            Move depth_best_move;
            
            // Get TT move if available
            Move* tt_move = nullptr;
            if (transposition_table.count(current_hash)) {
                tt_move = &transposition_table[current_hash].best_move;
            }
            
            order_moves(moves, isRed, 0, tt_move);
            
            bool completed_depth = false;
            for (const Move& move : moves) {
                if (!is_valid_move(move, isRed)) continue;

                current_time = chrono::steady_clock::now();
                elapsed = chrono::duration<double>(current_time - start_time).count();
                double hard_cap = urgent ? 0.95 : 0.85;
                if (elapsed > time_limit * hard_cap) {
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
    ZeroPointOneAI() : isRed(false), ourTurn(false), time_limit(30.0), total_time_used(0.0), move_count(0), current_hash(0) {
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

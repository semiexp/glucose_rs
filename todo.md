# TODO: glucose_rs 不足機能一覧

`semiexp/glucose`（C++）と現在の Rust 実装（`glucose_rs`）を比較して特定した未実装・不足機能をまとめます。

---

## 1. コアソルバー（`core/Solver`）の不足機能

### 1.1 仮定（Assumptions）付き求解
- C++ では `solve(const vec<Lit>& assumps)` / `solveLimited(const vec<Lit>& assumps)` が実装されており、仮定リテラルを与えて部分割り当て済みの状態から解を探せる。
- Rust 版の `solve()` は引数なしで仮定をサポートしない。
- UNSAT 時に仮定に基づいて導出された矛盾節を `conflict` フィールドに格納する機能も未実装。

### 1.2 リソース制約・割り込み
- `setConfBudget(int64_t x)` – 競合数の上限設定
- `setPropBudget(int64_t x)` – 伝播数の上限設定
- `budgetOff()` – 上限解除
- `interrupt()` / `clearInterrupt()` – 非同期割り込みフラグ
- `solveLimited()` – 上限に達した場合に `LBool::Undef` を返す制限付き求解
- これらはインクリメンタル SAT や外部タイムアウト制御に必須。

### 1.3 `simplify()` – 節簡約
- 決定レベル 0 で真になったリテラルを含む節を除去する前処理。
- C++ の `Solver::simplify()` に対応するメソッドが未実装。

### 1.4 変数・リテラルへの公開 API の不足
- `setPolarity(Var v, bool b)` – 決定ヒューリスティックの極性を外部から設定
- `setDecisionVar(Var v, bool b)` – 変数を決定候補から除外/追加
- `enqueue(Lit p, ...)` – 外部から強制的にリテラルを割り当てる公開 API
- `nAssigns()` / `nClauses()` / `nLearnts()` / `nVars()` / `nFreeVars()` – 状態照会メソッド
- `okay()` – ソルバーが矛盾状態かどうかの公開確認

### 1.5 変数の名前付け
- `newVar(bool polarity, bool dvar)` の引数が未対応（Rust 版は常にデフォルト値を使用）
- `newNamedVar(const std::string& name)` / `varName(Var x)` – 変数への名前付け機能が未実装

### 1.6 詳細な統計・ログ出力
- C++ では `verbosity`、`verbEveryConflicts`、`showModel` フラグによる詳細ログを持つ。
- `SolverStats.h` 相当の構造体と統計カウンタ群（`nbReduceDB`、`nbRemovedClauses`、`nbLearnts` 等）が未移植。
- `printIncrementalStats()` などの出力メソッドが未実装。

### 1.7 インクリメンタルモード
- `setIncrementalMode()` / `initNbInitialVars(int nb)` / `isIncremental()` – インクリメンタル SAT のための専用フラグと初期化が未実装。

### 1.8 高度な再起動・削減パラメータ
- `specialIncReduceDB`、`lbLBDFrozenClause`（LBD が低い節を削減から保護する閾値）未実装
- `chanseokStrategy` / `coLBDBound`（LBD ≤ coLBDBound の節を常に保持する戦略）未実装
- `lbSizeMinimizingClause` / `lbLBDMinimizingClause`（節最小化の条件パラメータ）未実装
- `max_var_decay`（変数 decay の上限値）未実装
- `luby_restart` / `adaptStrategies`（Luby 列再起動・適応型戦略切り替え）未実装
- `random_var_freq` / `random_seed`（確率的決定変数選択）未実装
- `glureduce` / `randomize_on_restarts` / `newDescent` 等のフラグが未移植

### 1.9 ガベージコレクション（節アリーナの圧縮）
- C++ では `RegionAllocator` ベースの節ストレージに対して `garbageCollect()` / `checkGarbage()` で断片化した節を圧縮する。
- Rust 版は `Vec<Clause>` の単純なアリーナで `deleted` フラグのみ立て、実際のメモリは解放しない。長時間実行時のメモリ消費が増大する。

### 1.10 DIMACS 出力
- `toDimacs(FILE* f, ...)` – 現在の問題を DIMACS 形式でファイルに書き出す機能が未実装。

---

## 2. 非節制約（`core/Constraint` フレームワーク）

C++ では `Constraint` 抽象基底クラスを通じて、節以外の任意の制約をソルバーに追加できる仕組みがある。Rust 版ではこのフレームワーク全体が未実装。

### 2.1 `Constraint` トレイト
- `initialize(solver)` / `propagate(solver, lit)` / `calcReason(solver, lit, extra, out_reason)` / `undo(solver, lit)` のインターフェース（トレイト）を定義する必要がある。
- `addConstraint(constraint)` – ソルバーへ制約を登録するメソッド
- `addWatch(lit, constraint)` / `registerUndo(var, constraint)` – 制約のウォッチ登録とアンドゥ登録
- `undoLists` – バックトラック時に制約の `undo` を呼ぶためのリスト

### 2.2 `AtMost` 制約（`constraints/AtMost`）
- リテラルリストのうち真になれる個数の上限を指定する at-most-k 制約。

### 2.3 `DirectEncodingExtension` 制約（`constraints/DirectEncodingExtension`）
- 直接エンコーディングを用いた整数変数の拡張制約。

### 2.4 `Graph` 制約（`constraints/Graph`）
- グラフの連結性・到達可能性に関する制約。

### 2.5 `GraphDivision` 制約（`constraints/GraphDivision`）
- グラフ分割（連結成分の分割数）に関する制約。

### 2.6 `OrderEncodingLinear` 制約（`constraints/OrderEncodingLinear`）
- オーダーエンコーディングによる線形算術制約。

### 2.7 `Xor` 制約（`constraints/Xor`）
- XOR（排他的論理和）制約。

---

## 3. 簡約ソルバー（`simp/SimpSolver`）

前処理により変数消去・節の包摂除去などを行う `SimpSolver` が未移植。

- **変数消去（Variable Elimination）** – 変数 v を含む節をレゾリューションにより消去する。
- **節の包摂除去（Subsumption Elimination）** – より強い節に包摂されている節を除去する。
- **自己包摂（Self-Subsumption）** – 節の強化（リテラルの削除）。
- `eliminate(turn_off_elim)` – 前処理エントリーポイント
- `setFrozen(var, frozen)` – 変数を消去対象から除外する
- `isEliminated(var)` – 変数が消去済みかどうか

---

## 4. 並列ソルバー（`parallel/`）

Syrup（Glucose Parallel）に対応する並列 CDCL ソルバーが未移植。

- `ParallelSolver` – スレッドごとのソルバーインスタンス（`Solver` の派生）
- `MultiSolvers` – 複数ソルバーを管理するオーケストレーター
- `SharedCompanion` – スレッド間での共有節（共有学習節バッファ）管理
- `SolverCompanion` / `SolverConfiguration` – ソルバー設定・調整
- `ClausesBuffer` – スレッド間で学習節を共有するロックフリーバッファ
- `parallelImportClauseDuringConflictAnalysis` / `parallelExportUnaryClause` 等のフック

---

## 5. テスト・品質

- 現状のテストはごく基本的な SAT/UNSAT テスト 5 件のみ。
- 仮定付き求解、インクリメンタル使用、制約付き求解のテストが未整備。
- C++ の `test/` に相当するベンチマーク・回帰テストが未移植。
- SAT Competition 形式の証明出力（DRUP/DRAT）が未実装（`certifiedUNSAT` フラグ相当）。

---

## 6. その他

- **`LBool` の `^` 演算子（`xor` との整合性）** – C++ の `lbool` は `^` 演算子で `sign` を適用する。現 Rust 実装は `xor` メソッドで代用しているが、演算子オーバーロードへの統一を検討。
- **`Lit::UNDEF` の使用** – センチネル値として `Lit::UNDEF` を多用しているが、`Option<Lit>` に置き換えることで安全性が増す。
- **`ClauseIdx` の `Option<ClauseIdx>` 化** – `CLAUSE_UNDEF` センチネルを `Option<ClauseIdx>` に置き換えることで Rust らしい安全な API になる。
- **`SolverTypes.h` の完全移植** – `Clause` の `mark` フィールドや `ExtraData`（`abstraction` / `act` 共用体）など、C++ の `Clause` 構造体にある詳細フィールドが未移植。

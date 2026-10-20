# 判定の原理：主張・形式命題・公理の対応（P001/P002の試し）

2026-10-19、Codex（研究R002）。[next-47](ARCHIVAL-REFERENCES.md#source-d662fa601494ef9b5d13)による1件だけの試し。
**有限単純グラフの局所条件を仮定した判定原理は接続済み。フラーレン曲面・全開始・実装への接続は未形式化。**
新しい証明・Lean実行は行わず、[既存AB対応](ARCHIVAL-REFERENCES.md#source-e1cb4d931a7b5a715db4)と保存済み監査を再利用した。

## P001：何を形式化したか

**自然言語。** [S0047](ARCHIVAL-REFERENCES.md#source-1d9b9fed85a8aa3df619) Def 1(a)の文字どおりの経路は、
相異なる2w個（w≥2）の頂点列で、連続頂点と一つ飛びの頂点が隣接し、両端が次数5、その隣が次数6である。
連続隣接は原文の「path」に、一つ飛び隣接は列挙条件に対応する。内部の次数5を禁止しない。
この読みの下で、固定した向き付き初期三角形からの経路が存在することは、強制列の最初の再訪Rより前に合法終点があることと同値。
原文の1始まりのv₁,…,v₂wをp(0),…,p(n)、n=2w−1とする。Rは**双対頂点数**以下であり、Rそのものを合法終点には使えない。

**主宣言。** `R002.finite_literal_path_decision`（[ソース](formal/Formal/FiniteLiteralPath.lean)）。
以下はnamespace `R002`、暗黙変数 `{V : Type*}` の下の宣言型（証明項を省略）。

```lean
theorem finite_literal_path_decision [Fintype V] (G : SimpleGraph V)
    (hG : TwoCommonNeighbors G) (cone : V → Prop) (t : OrderedTriangle G)
    (hc : cone t.a) (hb : ¬ cone t.b) :
    ∃ r ≤ Fintype.card V, FirstRepeat (forcedWalk G hG t) r ∧
      ((∃ n p, LiteralPathFrom G cone t p n) ↔
        ∃ e < r, LegalConeEndpoint cone (forcedWalk G hG t) e)
```

| 仮定・量化・定義 | 自然言語との対応／境界 |
|---|---|
| 任意の有限型V、`SimpleGraph V` | 有限な無向・ループなしの単純グラフ。平面性・双対性・次数5/6は型に含まれない |
| `TwoCommonNeighbors G` | 全ての隣接b,cに、互いに異なる共通隣接点x,yがあり、共通隣接点はその二つに限る。面の両側に三角形があるだけで、この仮定を満たしたことにはしない |
| 任意だが固定した`t`、`hc`、`hb` | `OrderedTriangle`はa-b、b-c、c-aの隣接。始点cone・第2点non-coneを仮定。全tについての適用は可能だが、適格な全開始を列挙する関数はこの定理にない |
| 任意の`cone : V → Prop` | 適用時にcone(v)⇔deg(v)=5と置く。¬cone(v)⇔deg(v)=6には**全頂点が次数5または6**という外側の証明が必要 |
| `LiteralPathFrom`、`FiniteTrianglePath` | n∈ℕ、p:ℕ→Vを存在量化。0..nの単射性・連続隣接・一つ飛び隣接、初期3点一致、始点と第2点、合法終点を要求。nより後は任意。有限経路の無限の単純な延長は仮定しない |
| `LegalConeEndpoint cone p e` | `3 ≤ e ∧ e % 2 = 1 ∧ cone (p e) ∧ ¬cone (p (e-1))`。頂点数e+1≥4は偶数。内部全点をnon-coneには制限しない |
| `FirstRepeat p r`、`PrefixInjective p n` | 前者は∃i<r,p(i)=p(r)、かつ全j<rで再訪なし。後者は閉区間0..nの単射性。`r≤card V`を存在量化し、終点は厳密にe<r。合法終点が全くない場合も同値に含む |

**接続済み。** [ForcedContinuation](formal/Formal/ForcedContinuation.lean)の`unique_other_common`から一意の次点と`forcedWalk`を構成。
`finite_path_no_backtrack` → `finite_path_eq_forced_prefix`で任意の有限経路をその列の前置列へ移し、
`forced_prefix_is_finite_path`・`legal_endpoint_of_prefix_eq`から`literal_path_iff_valid_forced_prefix`を得る。
[SequenceDecision](formal/Formal/SequenceDecision.lean)の`first_repeat_exists_bounded`・`valid_exists_iff_bounded_endpoint`を
`finite_forced_walk_decision`でつなぎ、主定理に至る。合法終点の最小値Eを使う別補題でも判定はE<Rで、E=Rは不成立。

**未接続。** ①実際のフラーレン双対から共通隣接点がちょうど二つ・次数5/6を導くこと、
②非IPRの第2点制約を含む全適格初期三角形の列挙と対称性還元、③チャート・接合・Python/C判定との対応。
`forcedWalk`は`Classical.choose`を使う**noncomputable**な定義で、定理もPropの存在同値である。
`DecidableRel G.Adj`や`DecidablePred cone`を仮定した実行可能な判定器を返してはいない。

## P002：何をどの環境で検査したか

固定環境は[lean-toolchain](formal/lean-toolchain)の`leanprover/lean4:v4.35.0`、
[lakefile](formal/lakefile.toml)のmathlib `v4.35.0`、[manifest](formal/lake-manifest.json)のcommit
`56a005855ea17e0b0958f73ec801ae140b0a1679`。現ローカルmathlibのHEADも一致する。
3設定ファイルとSequenceDecision・ForcedContinuationはT0519の基点commit `1f310255daf5a6d4fb1de19def3515835e690c6b`とバイト一致。
当時未追跡だった主ファイルはT0519/T0520のコード控えと現在版がhash一致する。両wrapper・保存ログのhashも照合した。

| 保存済み実行（再実行なし） | 正確なコマンドと結果 |
|---|---|
| [T0519](ARCHIVAL-REFERENCES.md#source-21c619bf36e3f1c2793e)・[stdout](ARCHIVAL-REFERENCES.md#source-072c2c1fe3a3eab766b8) | repo rootで `python3 historical-reference:source-13df6aed4582787bbaa3 historical-reference:source-34f249f7234661ae9a48`。子はcwd=`formal`で `lake env lean -j1 -M4096 historical-reference:source-34f249f7234661ae9a48`。終了0（ok）、14.897秒、1399.3MB |
| [T0520](evidence-eb108d11fc-T0520.json)・[stdout](evidence-f27446a97f-stdout.txt) | repo rootで `python3 historical-reference:source-7416b5a60e41bc4d42e4`。子はcwd=`formal`で `env LEAN_NUM_THREADS=1 lake --no-cache build +Formal:olean`。終了0（ok）、16.928秒、1488.9MB。主moduleはBuilt、関連2moduleはReplayed。header/module警告あり |

主ファイルの`#print axioms finite_literal_path_decision`の出力（T0519、T0520でも一致）：

```text
'R002.finite_literal_path_decision' depends on axioms: [propext, Classical.choice, Quot.sound]
```

| 分類 | この主宣言の推移的な出力 |
|---|---|
| 標準の数学的公理 | `propext`（命題外延性）、`Classical.choice`（選択）、`Quot.sound`（商の健全性） |
| 未完成・独自・native評価由来 | `sorryAx`なし、独自公理なし、native評価由来の追加公理なし。固定のnative名の検索ではなく、表示された全依存が上の3項だけであることを確認 |

**実施範囲。** T0519の対象ファイルの検査とT0520の統合build・公理出力を再利用した。
今回の作業は原文・型・依存関係の読解、保存版・hash・リンクの照合のみ。追加checker／外部kernelによる再検査は未実施。
公理出力は自然言語との対応や実装を保証しない。過去のLean実行バイナリのhashや全cacheの独立監査記録まではない。
R008の[S3002](ARCHIVAL-REFERENCES.md#source-51964e2fd3daf739573b)の控えは4.36.0-rc1を参照するため、そのnative公理名を4.35.0へ転用しない。

## 試しの評価（統括の追記欄を含む）

- 記入時間：3分24秒（初回資料読解の時刻採取 02:18:47〜02:22:11 JST）。読解・記入・保存記録の照合を含む壁時計時間で、純入力時間ではない。commit・連絡は含まない。
- 再整理した未接続・曖昧さ：`cone`と次数の二段の対応、原文「path」の連続隣接、固定開始と全開始の差、存在同値と実行可能判定器の差を明示できた。既知の境界の整理で、定理の反例・新しい証明は得ていない。
- 負担・効果：旧ABの記録を再利用でき、Lean再実行0・環境変更0・課金0。既存本文だけでは分散していた主宣言・公理・固定版・未接続を一箇所で追える形にした。読み手への効果は統括の点検待ち。
- 統括の追加質問・回答・点検所要時間：**未記入（統括が後で追記する。質問0件／点検済みとはしない）**。
- 初稿は[T0784](ARCHIVAL-REFERENCES.md#source-d7bb6bf58314711e8217)のmanual_viewに控えを固定し、このファイル末尾は統括の追記用に残す。完了をmailboxで知らせ、R002は再び待機する。

## 統括の点検と試しの評価（2026-10-19、Claude Code）

- **対応表は正確で、読みやすい。** Def 1(a)の各条件（相異なる偶数個、連続と一つ飛びの隣接、両端が次数5、その隣が次数6、内部の次数5を禁止しない）が、`hc`・`hb`・`LegalConeEndpoint`（`¬cone (p (e-1))`）・`FiniteTrianglePath` のどこに対応するかを一つずつ確かめられた。
- **試しで初めて明確になった点**：`forcedWalk` が noncomputable で、定理はPropの存在同値であり、実行できる判定器を返していないこと。「Leanで判定原理を確かめた」と書くときに、この区別を本文に添えるべきだと分かった。これは件数（98補題）だけでは見えなかった。
- **統括の追加の質問**：(1) 未接続①（フラーレン双対から `TwoCommonNeighbors` と次数5/6）は、既知の定理（巡回5辺連結性から分離三角形がない）を外部の仮定として明示した補題にできるか。(2) 同じ表を、論文の主定理の残り（A3の分類、直線定理）にも作れるか、その手間はどのくらいか。
- **評価**：記入・照合は3分24秒と小さく、効果（何が形式化済みで何が未接続かが一目で分かる）は大きい。**P001・P002は、論文に載せる主定理の標準として続ける価値がある**（最終判断は本人）。

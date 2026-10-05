# 環境構築

## Lean 4 のインストール

Lean 4 は **elan** というバージョン管理ツール経由でインストールします（Rust の rustup に相当します）。

```sh
curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh
```

Windows の場合は [Lean 4 公式のインストール手順](https://lean-lang.org/install/) を参照してください。VS Code を使う場合は拡張機能 **lean4** を入れると、拡張機能のほうから elan のインストールまで案内してくれます。

elan を入れると、プロジェクトごとの `lean-toolchain` ファイルに書かれたバージョンが自動的に使われます。Simplean は次のバージョンを使っています。

```text
{{#include ../../lean-toolchain}}
```

## リポジトリを取得してビルドする

```sh
git clone https://github.com/kmizu/simplean.git
cd simplean
lake build
```

`lake` は Lean 4 のビルドツールです。初回は依存関係の解決と全ファイルのコンパイル（証明の検査を含む）が走ります。Simplean は外部ライブラリに依存していないので、数十秒で終わります。

ビルド設定は `lakefile.toml` にあります。

```toml
{{#include ../../lakefile.toml}}
```

`autoImplicit = false` は「宣言していない変数を自動で導入しない」設定です。初心者には、タイプミスがそのまま新しい変数として解釈されてしまう事故を防いでくれるので、この本では常に無効にしています。

## VS Code で開く

VS Code で `simplean` フォルダを開き、任意の `.lean` ファイル（たとえば `Simplean/Examples.lean`）を開くと、右側に **Infoview** というパネルが出ます。これが Lean 4 を学ぶときの主役です。

- カーソルを `#eval` の行に置くと、評価結果が表示されます
- 証明の途中にカーソルを置くと、その時点の**ゴール**（示すべき命題）と**仮定**が表示されます

試しに `Simplean/Examples.lean` の末尾に次を書き足してみてください。

```lean
#eval evalProg factProg 100
```

Infoview に `Simplean.Res.ok (Simplean.Val.int 3628800)` と表示されれば、環境は整っています。`10!`（10 の階乗）を Simplean で計算した結果です。

## 自分の手で確かめる

この本の各章には `#eval` や `theorem … := by decide` が出てきます。写すだけでなく、数値や式を変えて、Infoview の表示がどう変わるかを見ることをお勧めします。Lean の学習で一番速いのは、**エラーメッセージを読む**ことです。付録 B に読み方をまとめてあります。

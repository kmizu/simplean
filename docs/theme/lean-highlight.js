// mdBook 同梱の highlight.js には Lean が無いので、Lean 4 用の簡易定義を後から登録して再ハイライトする。
(function () {
  if (typeof hljs === "undefined") return;
  hljs.registerLanguage("lean", function (hljs) {
    return {
      name: "Lean",
      keywords: {
        $pattern: /#?[\w'₀-₉]+|λ|∀|∃/,
        keyword:
          "theorem def abbrev inductive structure instance class where with match fun λ let have show by do " +
          "return if then else for in mutual end namespace section open deriving partial termination_by " +
          "decreasing_by macro syntax variable universe example import set_option at using " +
          "#eval #check #print #guard_msgs #reduce",
        built_in:
          "intro intros cases rcases induction simp simp_all simpa omega decide exact apply constructor obtain " +
          "rfl rw unfold split funext contradiction trivial assumption refine rintro next case repeat try first " +
          "all_goals subst subst_vars rename_i change exists use sorry dsimp",
        type: "Nat Int String List Option Bool Prop Type Unit Char",
        literal: "true false none some"
      },
      contains: [
        hljs.COMMENT("--", "$"),
        hljs.COMMENT("/-", "-/", { contains: ["self"] }),
        hljs.QUOTE_STRING_MODE,
        hljs.C_NUMBER_MODE,
        { className: "meta", begin: /@\[[^\]]*\]/ }
      ]
    };
  });
  function rehighlight() {
    document.querySelectorAll("code.language-lean").forEach(function (block) {
      block.removeAttribute("data-highlighted");
      if (hljs.highlightElement) hljs.highlightElement(block);
      else hljs.highlightBlock(block);
    });
  }
  if (document.readyState === "loading") {
    document.addEventListener("DOMContentLoaded", rehighlight);
  } else {
    rehighlight();
  }
})();

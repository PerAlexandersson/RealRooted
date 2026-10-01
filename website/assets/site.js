"use strict";

// Typeset $…$ and $$…$$ with KaTeX; Lean declarations in <pre>/<code> are skipped.
window.addEventListener("DOMContentLoaded", () => {
  if (typeof renderMathInElement !== "function") return;
  for (const element of document.querySelectorAll("main .prose")) {
    renderMathInElement(element, {
      delimiters: [
        { left: "$$", right: "$$", display: true },
        { left: "$", right: "$", display: false },
      ],
      throwOnError: false,
    });
  }
});

for (const control of document.querySelectorAll("[data-catalog-sort]")) {
  const lists = Array.from(control.closest("main")?.querySelectorAll("[data-catalog-list]") ?? []);
  if (!lists.length) continue;

  const compareName = (left, right) =>
    left.dataset.title.localeCompare(right.dataset.title, "en", { sensitivity: "base" });
  const compareYear = (left, right) => {
    const leftYear = Number(left.dataset.year) || Number.POSITIVE_INFINITY;
    const rightYear = Number(right.dataset.year) || Number.POSITIVE_INFINITY;
    return leftYear - rightYear || compareName(left, right);
  };

  control.addEventListener("change", (event) => {
    const selected = event.target.closest('input[type="radio"]');
    if (!selected) return;
    for (const list of lists) {
      const cards = Array.from(list.children);
      cards.sort(selected.value === "year" ? compareYear : compareName);
      list.append(...cards);
    }
  });
}

for (const control of document.querySelectorAll("[data-results-filter]")) {
  const main = control.closest("main");
  const rows = Array.from(main?.querySelectorAll("tbody tr") ?? []);
  const query = control.querySelector("[data-results-query]");
  const empty = main?.querySelector("[data-results-empty]");

  const update = () => {
    const words = (query?.value ?? "").toLocaleLowerCase("en").split(/\s+/).filter(Boolean);
    const kind = control.querySelector('input[name="results-kind"]:checked')?.value ?? "all";
    let shown = 0;
    for (const row of rows) {
      const visible =
        (kind === "all" || row.dataset.kind === kind) &&
        words.every((word) => row.dataset.search.includes(word));
      row.hidden = !visible;
      if (visible) shown += 1;
    }
    if (empty) empty.hidden = shown > 0;
  };

  control.addEventListener("input", update);
  control.addEventListener("change", update);
}

"use strict";

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

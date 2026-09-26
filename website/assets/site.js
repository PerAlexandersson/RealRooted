"use strict";

for (const control of document.querySelectorAll("[data-catalog-sort]")) {
  const list = control.closest("main")?.querySelector("[data-catalog-list]");
  if (!list) continue;

  const cards = Array.from(list.children);
  const compareName = (left, right) =>
    left.dataset.title.localeCompare(right.dataset.title, "en", { sensitivity: "base" });
  const compareYear = (left, right) => {
    const leftYear = Number(left.dataset.year) || Number.POSITIVE_INFINITY;
    const rightYear = Number(right.dataset.year) || Number.POSITIVE_INFINITY;
    return leftYear - rightYear || compareName(left, right);
  };

  control.addEventListener("change", () => {
    cards.sort(control.value === "year" ? compareYear : compareName);
    list.append(...cards);
  });
}

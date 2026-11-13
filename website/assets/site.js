"use strict";

// Typeset $…$ and $$…$$ with KaTeX; Lean declarations in <pre>/<code> are skipped.
window.addEventListener("DOMContentLoaded", () => {
  if (typeof renderMathInElement !== "function") return;
  for (const element of document.querySelectorAll("main .prose")) {
    renderMathInElement(element, {
      delimiters: [
        { left: "$$", right: "$$", display: true },
        { left: "\\[", right: "\\]", display: true },
        { left: "$", right: "$", display: false },
        { left: "\\(", right: "\\)", display: false },
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
  const compareNewest = (left, right) =>
    right.dataset.formalized.localeCompare(left.dataset.formalized) || compareName(left, right);

  control.addEventListener("change", (event) => {
    const selected = event.target.closest('input[type="radio"]');
    if (!selected) return;
    for (const list of lists) {
      const cards = Array.from(list.children);
      cards.sort(
        selected.value === "year" ? compareYear :
        selected.value === "newest" ? compareNewest : compareName,
      );
      list.append(...cards);
    }
  });
}

// Both entry points use the same complete, normalized index. No search libraries.
for (const control of document.querySelectorAll("[data-catalog-search]")) {
  const main = control.closest("main");
  const query = control.querySelector("[data-catalog-query]");
  const status = control.querySelector("[data-search-status]");
  const matchesSection = main.querySelector("[data-search-matches]");
  const list = main.querySelector("[data-search-list]");
  const more = main.querySelector("[data-search-more]");
  const kindControl = main.querySelector("[data-results-filter]");
  const browsing = Array.from(main.querySelectorAll("[data-results-browse]"));
  const cards = Array.from(main.querySelectorAll(".catalog-card"));
  const groups = Array.from(main.querySelectorAll(".catalog-group"));
  const topicLinks = Array.from(main.querySelectorAll(".topic-jump a"));
  const landingControls = cards.length ? Array.from(
    main.querySelectorAll(".topic-jump, [data-catalog-sort]")) : [];
  const normalize = (value) => value.normalize("NFD").replace(/[\u0300-\u036f]/g, "")
    .toLocaleLowerCase("en");
  let index;
  let pending;
  let matches = [];
  let shown = 0;
  let timer;
  const batchSize = 50;

  const appendResults = () => {
    const fragment = document.createDocumentFragment();
    for (const item of matches.slice(shown, shown + batchSize)) {
      const page = index.pages[item.page];
      const row = document.createElement("li");
      const link = document.createElement("a");
      link.href = item.url;
      link.textContent = item.label || item.name;
      const details = document.createElement("span");
      details.className = "search-detail";
      details.textContent = `${page.title} · ${item.kind}${item.headline ? " · Main result" : ""}`;
      const name = document.createElement("code");
      name.textContent = item.name;
      row.append(link, details, name);
      fragment.append(row);
    }
    list.append(fragment);
    shown = Math.min(shown + batchSize, matches.length);
    more.hidden = shown >= matches.length;
    // Retain the button (and keyboard focus) when the final batch is appended.
    if (shown >= matches.length && document.activeElement === more) {
      more.hidden = false;
      more.disabled = true;
      more.textContent = "All matching declarations shown";
    }
  };

  const restoreBrowsing = () => {
    browsing.forEach((element) => { element.hidden = false; });
    cards.forEach((card) => { card.hidden = false; });
    groups.forEach((group) => { group.hidden = false; });
    topicLinks.forEach((link) => { link.hidden = false; });
    landingControls.forEach((element) => { element.hidden = false; });
    matchesSection.hidden = true;
  };

  const update = () => {
    const words = normalize(query.value).split(/\s+/).filter(Boolean);
    const kind = kindControl?.querySelector('input[name="results-kind"]:checked')?.value ?? "all";
    if (!words.length && kind === "all") {
      restoreBrowsing();
      status.textContent = "Search all pages and selected declarations.";
      return;
    }
    if (!index) {
      status.textContent = "Loading catalog search…";
      loadIndex();
      return;
    }
    const includes = (text) => words.every((word) => text.includes(word));
    matches = index.declarations.filter((item) =>
      (kind === "all" || (kind === "headline" ? item.headline : item.kind === kind)) &&
      includes(item.search));
    const pageMatches = new Set(index.pages.filter((page) => includes(page.search)).map((p) => p.slug));
    matches.forEach((item) => pageMatches.add(index.pages[item.page].slug));
    cards.forEach((card) => { card.hidden = !pageMatches.has(card.dataset.slug); });
    groups.forEach((group) => {
      group.hidden = !Array.from(group.querySelectorAll(".catalog-card")).some((card) => !card.hidden);
    });
    topicLinks.forEach((link) => {
      link.hidden = document.querySelector(link.hash)?.hidden ?? false;
    });
    landingControls.forEach((element) => { element.hidden = pageMatches.size === 0; });
    browsing.forEach((element) => { element.hidden = true; });
    matchesSection.hidden = false;
    list.replaceChildren();
    shown = 0;
    more.disabled = false;
    more.textContent = "Show more results";
    appendResults();
    status.textContent = `${matches.length} matching declaration${matches.length === 1 ? "" : "s"}` +
      (cards.length ? ` · ${pageMatches.size} matching page${pageMatches.size === 1 ? "" : "s"}` : "") +
      (matches.length > batchSize ? ` · Showing the first ${batchSize}; use Show more results.` : ".") +
      (!matches.length && !pageMatches.size ? " No matches. Try another name or fewer words." : "");
  };

  const loadIndex = () => {
    if (pending) return;
    pending = fetch(control.dataset.catalogSearch).then((response) => {
      if (!response.ok) throw new Error("Search index unavailable");
      return response.json();
    }).then((data) => {
      index = data;
      for (const page of index.pages) {
        page.shared = normalize([page.title, page.headline, ...page.authors, ...page.years,
          page.topic, ...page.symcat, ...page.objects].join(" "));
        page.search = `${page.shared} ${normalize(page.labels.join(" "))}`;
      }
      for (const item of index.declarations) {
        item.search = `${index.pages[item.page].shared} ${normalize([item.name, item.label,
          item.symcat, ...item.objects, ...item.tags].join(" "))}`;
      }
      update();
    }).catch(() => {
      index = undefined;
      pending = undefined;
      restoreBrowsing();
      status.textContent = "Search could not load. Browse the links below or type again to retry.";
    });
  };

  query.addEventListener("focus", loadIndex);
  query.addEventListener("input", () => {
    clearTimeout(timer);
    timer = setTimeout(update, 100);
  });
  kindControl?.addEventListener("change", update);
  more.addEventListener("click", () => {
    appendResults();
    status.textContent = `Showing ${shown} of ${matches.length} matching declarations.`;
  });
  if (window.location.hash === "#main-results") {
    const headline = kindControl?.querySelector('input[value="headline"]');
    if (headline) { headline.checked = true; update(); }
  }
}

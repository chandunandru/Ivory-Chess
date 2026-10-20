"use strict";

/* ---------- Constants ---------- */

const FILES = "abcdefgh";

const COLOR_NAMES = {
  w: "White",
  b: "Black"
};

const PIECE_NAMES = {
  K: "King",
  Q: "Queen",
  R: "Rook",
  B: "Bishop",
  N: "Knight",
  P: "Pawn"
};

/*
  Filled symbols are used for both sides.
  CSS gives each side its own color and depth.
*/
const SYMBOLS = {
  K: "♚",
  Q: "♛",
  R: "♜",
  B: "♝",
  N: "♞",
  P: "♟"
};

const ORTHOGONAL = [
  [-1, 0],
  [1, 0],
  [0, -1],
  [0, 1]
];

const DIAGONAL = [
  [-1, -1],
  [-1, 1],
  [1, -1],
  [1, 1]
];

const DIRECTIONS = [...ORTHOGONAL, ...DIAGONAL];

const KNIGHT_STEPS = [
  [-2, -1],
  [-2, 1],
  [-1, -2],
  [-1, 2],
  [1, -2],
  [1, 2],
  [2, -1],
  [2, 1]
];

const ROOK_RIGHTS = {
  0: "bQ",
  7: "bK",
  56: "wQ",
  63: "wK"
};

/* ---------- DOM ---------- */

const ui = {
  board: document.getElementById("board"),
  stage: document.getElementById("board-stage"),
  status: document.getElementById("game-status"),
  detail: document.getElementById("game-detail"),
  turnDot: document.getElementById("turn-dot"),
  moveNumber: document.getElementById("move-number"),
  moveList: document.getElementById("move-list"),
  moveCount: document.getElementById("move-count"),
  emptyHistory: document.getElementById("empty-history"),
  historyScroll: document.getElementById("history-scroll"),
  undo: document.getElementById("undo-move"),
  redo: document.getElementById("redo-move"),
  claim: document.getElementById("claim-draw"),
  promotion: document.getElementById("promotion-dialog"),
  promotionOptions: document.getElementById("promotion-options")
};

/* ---------- Game state ---------- */

let state = createInitialState();
let history = [];
let redoHistory = [];

let selected = null;
let flipped = false;
let is3D = true;

let legalCache = [];
let gameOver = false;

let pendingPromotion = null;
let claimReason = "";
let claimedDraw = "";
let animatedMove = null;
let useViewTransition = false;
let animatedRestoreIndex = null;

/* ---------- Helpers ---------- */

function opposite(color) {
  return color === "w" ? "b" : "w";
}

function row(index) {
  return Math.floor(index / 8);
}

function col(index) {
  return index % 8;
}

function inside(r, c) {
  return r >= 0 && r < 8 && c >= 0 && c < 8;
}

function squareName(index) {
  return FILES[col(index)] + (8 - row(index));
}

function createInitialState() {
  const board = Array(64).fill(null);
  const backRank = "RNBQKBNR";

  for (let c = 0; c < 8; c++) {
    board[c] = "b" + backRank[c];
    board[8 + c] = "bP";

    board[48 + c] = "wP";
    board[56 + c] = "w" + backRank[c];
  }

  return {
    board,
    turn: "w",
    castling: {
      wK: true,
      wQ: true,
      bK: true,
      bQ: true
    },
    ep: null,
    halfmove: 0,
    fullmove: 1,
    last: null
  };
}

/* ---------- Attack detection ---------- */

function isAttacked(s, target, byColor) {
  const tr = row(target);
  const tc = col(target);

  // Pawns attack diagonally, not straight ahead.
  const pawnRow = tr + (byColor === "w" ? 1 : -1);

  for (const dc of [-1, 1]) {
    const c = tc + dc;

    if (
      inside(pawnRow, c) &&
      s.board[pawnRow * 8 + c] === byColor + "P"
    ) {
      return true;
    }
  }

  // Knights.
  for (const [dr, dc] of KNIGHT_STEPS) {
    const r = tr + dr;
    const c = tc + dc;

    if (
      inside(r, c) &&
      s.board[r * 8 + c] === byColor + "N"
    ) {
      return true;
    }
  }

  // Sliding pieces and adjacent kings.
  for (const [dr, dc] of DIRECTIONS) {
    let r = tr + dr;
    let c = tc + dc;
    let distance = 1;

    while (inside(r, c)) {
      const piece = s.board[r * 8 + c];

      if (piece) {
        if (piece[0] === byColor) {
          const kind = piece[1];
          const diagonal = dr !== 0 && dc !== 0;

          if (kind === "K" && distance === 1) {
            return true;
          }

          if (
            kind === "Q" ||
            (diagonal && kind === "B") ||
            (!diagonal && kind === "R")
          ) {
            return true;
          }
        }

        break;
      }

      r += dr;
      c += dc;
      distance++;
    }
  }

  return false;
}

function inCheck(s, color) {
  const king = s.board.indexOf(color + "K");

  return king === -1 || isAttacked(s, king, opposite(color));
}

/* ---------- Move generation ---------- */

function pseudoMoves(s, from) {
  const piece = s.board[from];

  if (!piece) {
    return [];
  }

  const color = piece[0];
  const kind = piece[1];
  const enemy = opposite(color);

  const r = row(from);
  const c = col(from);

  const moves = [];

  function add(to, extra = {}) {
    // Generate all four promotion choices.
    if (kind === "P" && (row(to) === 0 || row(to) === 7)) {
      for (const promotion of ["Q", "R", "B", "N"]) {
        moves.push({
          from,
          to,
          ...extra,
          promotion
        });
      }
    } else {
      moves.push({
        from,
        to,
        ...extra
      });
    }
  }

  // Pawns.
  if (kind === "P") {
    const direction = color === "w" ? -1 : 1;
    const startingRow = color === "w" ? 6 : 1;
    const nextRow = r + direction;

    if (
      inside(nextRow, c) &&
      !s.board[nextRow * 8 + c]
    ) {
      add(nextRow * 8 + c);

      const doubleRow = r + direction * 2;

      if (
        r === startingRow &&
        !s.board[doubleRow * 8 + c]
      ) {
        add(doubleRow * 8 + c);
      }
    }

    for (const dc of [-1, 1]) {
      const captureCol = c + dc;

      if (!inside(nextRow, captureCol)) {
        continue;
      }

      const to = nextRow * 8 + captureCol;
      const target = s.board[to];

      if (
        target &&
        target[0] === enemy &&
        target[1] !== "K"
      ) {
        add(to);
      } else if (
        !target &&
        to === s.ep &&
        s.board[r * 8 + captureCol] === enemy + "P"
      ) {
        add(to, { enPassant: true });
      }
    }

    return moves;
  }

  // Knights and kings.
  if (kind === "N" || kind === "K") {
    const steps = kind === "N" ? KNIGHT_STEPS : DIRECTIONS;

    for (const [dr, dc] of steps) {
      const nr = r + dr;
      const nc = c + dc;

      if (!inside(nr, nc)) {
        continue;
      }

      const to = nr * 8 + nc;
      const target = s.board[to];

      if (
        !target ||
        (target[0] !== color && target[1] !== "K")
      ) {
        add(to);
      }
    }

    if (kind === "N") {
      return moves;
    }

    // Castling.
    const home = color === "w" ? 60 : 4;

    if (from !== home || inCheck(s, color)) {
      return moves;
    }

    if (
      s.castling[color + "K"] &&
      s.board[home + 3] === color + "R" &&
      !s.board[home + 1] &&
      !s.board[home + 2] &&
      !isAttacked(s, home + 1, enemy) &&
      !isAttacked(s, home + 2, enemy)
    ) {
      add(home + 2, { castle: "K" });
    }

    if (
      s.castling[color + "Q"] &&
      s.board[home - 4] === color + "R" &&
      !s.board[home - 1] &&
      !s.board[home - 2] &&
      !s.board[home - 3] &&
      !isAttacked(s, home - 1, enemy) &&
      !isAttacked(s, home - 2, enemy)
    ) {
      add(home - 2, { castle: "Q" });
    }

    return moves;
  }

  // Bishops, rooks, and queens.
  const directions =
    kind === "B"
      ? DIAGONAL
      : kind === "R"
        ? ORTHOGONAL
        : DIRECTIONS;

  for (const [dr, dc] of directions) {
    let nr = r + dr;
    let nc = c + dc;

    while (inside(nr, nc)) {
      const to = nr * 8 + nc;
      const target = s.board[to];

      if (!target) {
        add(to);
      } else {
        if (target[0] !== color && target[1] !== "K") {
          add(to);
        }

        break;
      }

      nr += dr;
      nc += dc;
    }
  }

  return moves;
}

/* ---------- Apply a move without mutating the old state ---------- */

function applyMove(s, move) {
  const piece = s.board[move.from];
  const color = piece[0];
  const kind = piece[1];
  const captured = s.board[move.to];

  const next = {
    ...s,
    board: s.board.slice(),
    castling: { ...s.castling },
    ep: null,
    last: {
      from: move.from,
      to: move.to
    }
  };

  next.board[move.from] = null;

  if (move.enPassant) {
    const capturedSquare =
      move.to + (color === "w" ? 8 : -8);

    next.board[capturedSquare] = null;
  }

  next.board[move.to] = color + (move.promotion || kind);

  if (move.castle) {
    const rookFrom =
      move.castle === "K"
        ? move.from + 3
        : move.from - 4;

    const rookTo =
      move.castle === "K"
        ? move.from + 1
        : move.from - 1;

    next.board[rookTo] = next.board[rookFrom];
    next.board[rookFrom] = null;
  }

  if (kind === "K") {
    next.castling[color + "K"] = false;
    next.castling[color + "Q"] = false;
  }

  // Moving or capturing a corner rook removes that castling right.
  for (const square of [move.from, move.to]) {
    const right = ROOK_RIGHTS[square];

    if (right) {
      next.castling[right] = false;
    }
  }

  if (
    kind === "P" &&
    Math.abs(move.to - move.from) === 16
  ) {
    next.ep = (move.from + move.to) / 2;
  }

  next.halfmove =
    kind === "P" || captured
      ? 0
      : s.halfmove + 1;

  next.fullmove =
    s.fullmove + (color === "b" ? 1 : 0);

  next.turn = opposite(color);

  return next;
}

function allLegalMoves(s) {
  const moves = [];

  for (let from = 0; from < 64; from++) {
    const piece = s.board[from];

    if (!piece || piece[0] !== s.turn) {
      continue;
    }

    for (const move of pseudoMoves(s, from)) {
      const next = applyMove(s, move);

      if (!inCheck(next, s.turn)) {
        moves.push(move);
      }
    }
  }

  return moves;
}

/* ---------- Notation ---------- */

function moveNotation(before, move, after) {
  const piece = before.board[move.from];
  const kind = piece[1];

  let text = "";

  if (move.castle) {
    text = move.castle === "K" ? "O-O" : "O-O-O";
  } else {
    const capture =
      Boolean(before.board[move.to]) ||
      Boolean(move.enPassant);

    let prefix = kind === "P" ? "" : kind;

    if (kind === "P" && capture) {
      prefix = FILES[col(move.from)];
    }

    if (kind !== "P") {
      const rivals = allLegalMoves(before).filter(candidate => {
        return (
          candidate.from !== move.from &&
          candidate.to === move.to &&
          before.board[candidate.from] === piece
        );
      });

      if (rivals.length) {
        const fileIsUnique = rivals.every(candidate => {
          return col(candidate.from) !== col(move.from);
        });

        const rankIsUnique = rivals.every(candidate => {
          return row(candidate.from) !== row(move.from);
        });

        if (fileIsUnique) {
          prefix += FILES[col(move.from)];
        } else if (rankIsUnique) {
          prefix += 8 - row(move.from);
        } else {
          prefix += squareName(move.from);
        }
      }
    }

    text =
      prefix +
      (capture ? "x" : "") +
      squareName(move.to) +
      (move.promotion ? "=" + move.promotion : "");
  }

  if (inCheck(after, after.turn)) {
    text += allLegalMoves(after).length ? "+" : "#";
  }

  return text;
}

/* ---------- Draw handling ---------- */

function positionKey(s, legalMoves) {
  const boardKey = s.board
    .map(piece => piece || "..")
    .join("");

  const rights = ["wK", "wQ", "bK", "bQ"]
    .map(right => (s.castling[right] ? "1" : "0"))
    .join("");

  // An en passant square affects repetition only when capture is legal.
  const ep = legalMoves.some(move => move.enPassant)
    ? s.ep
    : "-";

  return `${boardKey}|${s.turn}|${rights}|${ep}`;
}

function insufficientMaterial(s) {
  const pieces = [];

  s.board.forEach((piece, index) => {
    if (piece && piece[1] !== "K") {
      pieces.push({ piece, index });
    }
  });

  if (pieces.length === 0) {
    return true;
  }

  if (
    pieces.length === 1 &&
    ["B", "N"].includes(pieces[0].piece[1])
  ) {
    return true;
  }

  // Only bishops remaining, all on the same square color.
  if (pieces.every(entry => entry.piece[1] === "B")) {
    const colors = new Set(
      pieces.map(entry => {
        return (row(entry.index) + col(entry.index)) % 2;
      })
    );

    return colors.size === 1;
  }

  return false;
}

/* ---------- Rendering ---------- */

function renderBoard(checked) {
  const activeElement = document.activeElement;

  const focusedSquare =
    activeElement &&
    ui.board.contains(activeElement) &&
    activeElement.dataset.index !== undefined
      ? Number(activeElement.dataset.index)
      : null;

  const targets = new Map(
    legalCache
      .filter(move => move.from === selected)
      .map(move => [move.to, move])
  );

  const checkedKing = checked
    ? state.board.indexOf(state.turn + "K")
    : -1;

  const fragment = document.createDocumentFragment();

  for (let visualIndex = 0; visualIndex < 64; visualIndex++) {
    const index = flipped ? 63 - visualIndex : visualIndex;

    const r = row(index);
    const c = col(index);

    const visualRow = row(visualIndex);
    const visualCol = col(visualIndex);

    const piece = state.board[index];

    const square = document.createElement("button");
    square.type = "button";
    square.dataset.index = index;

    square.className =
      "square " + ((r + c) % 2 === 0 ? "light" : "dark");

    square.disabled = gameOver;

    if (index === selected) {
      square.classList.add("selected");
    }

    if (
      state.last &&
      (index === state.last.from || index === state.last.to)
    ) {
      square.classList.add("last-move");
    }

    if (index === checkedKing) {
      square.classList.add("in-check");
    }

    if (targets.has(index)) {
      square.classList.add("legal");

      if (piece || targets.get(index).enPassant) {
        square.classList.add("capture");
      }
    }

    const description = piece
      ? `${COLOR_NAMES[piece[0]]} ${PIECE_NAMES[piece[1]]}`
      : "Empty";

    square.setAttribute(
      "aria-label",
      `${squareName(index)}: ${description}` +
      (targets.has(index) ? ", legal destination" : "")
    );

    square.setAttribute(
      "aria-pressed",
      String(index === selected)
    );

    if (piece) {
      const symbol = document.createElement("span");

      symbol.className =
        "piece " +
        (piece[0] === "w" ? "white-piece" : "black-piece");

      if (animatedMove && index === animatedMove.to) {
        if (useViewTransition) {
          symbol.style.viewTransitionName = "moving-chess-piece";
        } else {
          symbol.classList.add("piece-arrived");
        }
      }

      if (animatedRestoreIndex === index) {
        if (useViewTransition) {
          symbol.style.viewTransitionName = "restored-chess-piece";
        } else {
          symbol.classList.add("piece-arrived");
        }
      }

      symbol.textContent = SYMBOLS[piece[1]] + "\uFE0E";
      symbol.setAttribute("aria-hidden", "true");

      square.appendChild(symbol);
    }

    if (visualCol === 0) {
      const rank = document.createElement("span");

      rank.className = "coordinate rank";
      rank.textContent = 8 - r;
      rank.setAttribute("aria-hidden", "true");

      square.appendChild(rank);
    }

    if (visualRow === 7) {
      const file = document.createElement("span");

      file.className = "coordinate file";
      file.textContent = FILES[c];
      file.setAttribute("aria-hidden", "true");

      square.appendChild(file);
    }

    square.addEventListener("click", () => {
      handleSquareClick(index);
    });

    fragment.appendChild(square);
  }

  ui.board.replaceChildren(fragment);

  // Keep keyboard focus when the board is redrawn.
  if (focusedSquare !== null && !gameOver) {
    const button = ui.board.querySelector(
      `[data-index="${focusedSquare}"]`
    );

    button?.focus({ preventScroll: true });
  }
}

function renderPlayerBar(id, color) {
  const bar = document.getElementById(id);
  const active = !gameOver && state.turn === color;

  bar.classList.toggle("active", active);

  bar.querySelector(".player-dot").className =
    "player-dot " + color;

  bar.querySelector("strong").textContent =
    COLOR_NAMES[color];

  bar.querySelector(".player-note").textContent =
    active ? "To move" : "Local player";
}

function renderHistory() {
  ui.moveList.replaceChildren();

  ui.emptyHistory.hidden = history.length > 0;

  ui.moveCount.textContent =
    `${history.length} ` +
    (history.length === 1 ? "move" : "moves");

  const fragment = document.createDocumentFragment();

  for (let i = 0; i < history.length; i += 2) {
    const entry = document.createElement("li");

    const values = [
      `${i / 2 + 1}.`,
      history[i].label,
      history[i + 1]?.label || "—"
    ];

    values.forEach((value, index) => {
      const span = document.createElement("span");
      span.textContent = value;

      if (index === 0) {
        span.className = "move-index";
      }

      entry.appendChild(span);
    });

    fragment.appendChild(entry);
  }

  ui.moveList.appendChild(fragment);
}

function render() {
  legalCache = allLegalMoves(state);

  const checked = inCheck(state, state.turn);
  const key = positionKey(state, legalCache);

  const repetitions = history.reduce((count, entry) => {
    return count + (entry.key === key ? 1 : 0);
  }, 1);

  let outcome = null;

  // Checkmate takes priority over automatic move-count draws.
  if (legalCache.length === 0) {
    outcome = checked
      ? {
          title: `${COLOR_NAMES[opposite(state.turn)]} wins`,
          detail: "Checkmate. Start a new game or undo a move."
        }
      : {
          title: "Draw — stalemate",
          detail: "There are no legal moves, but the king is not in check."
        };
  } else if (insufficientMaterial(state)) {
    outcome = {
      title: "Draw",
      detail: "Insufficient material to deliver checkmate."
    };
  } else if (repetitions >= 5) {
    outcome = {
      title: "Draw",
      detail: "Automatic draw by fivefold repetition."
    };
  } else if (state.halfmove >= 150) {
    outcome = {
      title: "Draw",
      detail: "Automatic draw under the 75-move rule."
    };
  } else if (claimedDraw) {
    outcome = {
      title: "Draw claimed",
      detail: claimedDraw + "."
    };
  }

  gameOver = Boolean(outcome);

  claimReason = "";

  if (!gameOver) {
    if (repetitions >= 3) {
      claimReason = "Threefold repetition";
    } else if (state.halfmove >= 100) {
      claimReason = "50-move rule";
    }
  }

  ui.status.textContent = outcome
    ? outcome.title
    : `${COLOR_NAMES[state.turn]} to move`;

  ui.detail.textContent = outcome
    ? outcome.detail
    : checked
      ? `${COLOR_NAMES[state.turn]} is in check. Protect your king.`
      : "Select a piece to see its legal moves.";

  if (claimReason) {
    ui.detail.textContent += " A draw can now be claimed.";
  }

  ui.turnDot.className =
    "turn-dot " + (gameOver ? "finished" : state.turn);

  ui.moveNumber.textContent = `Move ${state.fullmove}`;

  ui.undo.disabled = history.length === 0;
  ui.redo.disabled = redoHistory.length === 0;
  ui.claim.hidden = !claimReason;

  renderBoard(checked);

  const topColor = flipped ? "w" : "b";

  renderPlayerBar("top-player", topColor);
  renderPlayerBar("bottom-player", opposite(topColor));

  renderHistory();
}

function renderMove(move, { captureIndex = null, restoredIndex = null } = {}) {
  const sourcePiece = ui.board.querySelector(
    `[data-index="${move.from}"] .piece`
  );
  const capturedPiece = captureIndex === null
    ? null
    : ui.board.querySelector(
        `[data-index="${captureIndex}"] .piece`
      );
  const capturedGhost = capturedPiece?.cloneNode(true) || null;

  const canUseViewTransition =
    typeof document.startViewTransition === "function" &&
    !window.matchMedia("(prefers-reduced-motion: reduce)").matches;

  if (canUseViewTransition && sourcePiece) {
    sourcePiece.style.viewTransitionName = "moving-chess-piece";

    if (capturedPiece) {
      capturedPiece.style.viewTransitionName = "captured-chess-piece";
    }

    document.startViewTransition(() => {
      animatedMove = move;
      animatedRestoreIndex = restoredIndex;
      useViewTransition = true;
      render();
      animateCapture(captureIndex, capturedGhost, !canUseViewTransition);
      animatedMove = null;
      animatedRestoreIndex = null;
      useViewTransition = false;
    });
  } else {
    animatedMove = move;
    animatedRestoreIndex = restoredIndex;
    render();
    animateCapture(captureIndex, capturedGhost, true);
    animatedMove = null;
    animatedRestoreIndex = null;
  }
}

function animateCapture(captureIndex, capturedGhost, useGhost) {
  if (
    captureIndex === null ||
    window.matchMedia("(prefers-reduced-motion: reduce)").matches
  ) {
    return;
  }

  const impactSquare = ui.board.querySelector(
    `[data-index="${animatedMove.to}"]`
  );

  impactSquare?.classList.add("capture-impact");
  impactSquare?.addEventListener("animationend", () => {
    impactSquare.classList.remove("capture-impact");
  }, { once: true });

  if (!useGhost || !capturedGhost) {
    return;
  }

  const capturedSquare = ui.board.querySelector(
    `[data-index="${captureIndex}"]`
  );

  capturedGhost.classList.add("capture-ghost");
  capturedGhost.style.viewTransitionName = "";
  capturedSquare?.appendChild(capturedGhost);
  capturedGhost.addEventListener("animationend", () => {
    capturedGhost.remove();
  }, { once: true });
}

/* ---------- Interaction ---------- */

function handleSquareClick(index) {
  if (gameOver || pendingPromotion) {
    return;
  }

  const move = selected !== null
    ? legalCache.find(candidate => {
        return (
          candidate.from === selected &&
          candidate.to === index
        );
      })
    : null;

  if (move) {
    if (move.promotion) {
      openPromotion(move);
    } else {
      commitMove(move);
    }

    return;
  }

  const piece = state.board[index];

  if (piece && piece[0] === state.turn) {
    selected = selected === index ? null : index;
  } else {
    selected = null;
  }

  render();
}

function commitMove(move) {
  const before = state;
  const after = applyMove(before, move);
  const capturedIndex = move.enPassant
    ? move.to + (before.turn === "w" ? 8 : -8)
    : move.to;
  const capturedPiece = before.board[capturedIndex];
  const captureIndex = capturedPiece ? capturedIndex : null;

  history.push({
    move,
    before,
    after,
    captureIndex,
    key: positionKey(before, legalCache),
    label: moveNotation(before, move, after)
  });

  state = after;
  redoHistory = [];

  selected = null;
  claimedDraw = "";

  renderMove(move, { captureIndex });

  ui.historyScroll.scrollTop =
    ui.historyScroll.scrollHeight;
}

ui.stage.addEventListener("pointermove", event => {
  if (event.pointerType === "touch" || ui.stage.classList.contains("flat")) {
    return;
  }

  const bounds = ui.stage.getBoundingClientRect();
  const horizontal = (event.clientX - bounds.left) / bounds.width - 0.5;
  const vertical = (event.clientY - bounds.top) / bounds.height - 0.5;

  ui.stage.style.setProperty("--tilt-y", `${horizontal * 3.5}deg`);
  ui.stage.style.setProperty("--tilt-x", `${vertical * -2.5}deg`);
  ui.stage.style.setProperty("--shift-x", `${horizontal * 2.5}px`);
  ui.stage.style.setProperty("--shift-y", `${vertical * 2}px`);
});

ui.stage.addEventListener("pointerleave", () => {
  ui.stage.style.removeProperty("--tilt-x");
  ui.stage.style.removeProperty("--tilt-y");
  ui.stage.style.removeProperty("--shift-x");
  ui.stage.style.removeProperty("--shift-y");
});

function openPromotion(move) {
  pendingPromotion = move;
  ui.promotionOptions.replaceChildren();

  for (const kind of ["Q", "R", "B", "N"]) {
    const button = document.createElement("button");
    button.type = "button";
    button.className = "promotion-option";

    const symbol = document.createElement("span");

    symbol.className =
      "promotion-symbol " +
      (state.turn === "w" ? "white-piece" : "black-piece");

    symbol.textContent = SYMBOLS[kind] + "\uFE0E";
    symbol.setAttribute("aria-hidden", "true");

    const label = document.createElement("span");
    label.textContent = PIECE_NAMES[kind];

    button.append(symbol, label);

    button.addEventListener("click", () => {
      if (!pendingPromotion) {
        return;
      }

      const chosenMove = {
        ...pendingPromotion,
        promotion: kind
      };

      pendingPromotion = null;
      ui.promotion.close();

      commitMove(chosenMove);
    });

    ui.promotionOptions.appendChild(button);
  }

  ui.promotion.showModal();
}

/* Escape cancels the uncommitted promotion move. */
ui.promotion.addEventListener("cancel", event => {
  event.preventDefault();

  pendingPromotion = null;
  selected = null;

  ui.promotion.close();
  render();
});

document.getElementById("new-game").addEventListener("click", () => {
  if (
    history.length > 0 &&
    !window.confirm("Start a new game? Current progress will be lost.")
  ) {
    return;
  }

  state = createInitialState();
  history = [];
  redoHistory = [];

  selected = null;
  pendingPromotion = null;
  claimedDraw = "";

  if (ui.promotion.open) {
    ui.promotion.close();
  }

  render();
});

ui.undo.addEventListener("click", () => {
  const previous = history.pop();

  if (!previous) {
    return;
  }

  redoHistory.push(previous);
  state = previous.before;

  selected = null;
  pendingPromotion = null;
  claimedDraw = "";

  renderMove({
    from: previous.move.to,
    to: previous.move.from
  }, {
    restoredIndex: previous.captureIndex
  });
});

ui.redo.addEventListener("click", () => {
  const next = redoHistory.pop();

  if (!next) {
    return;
  }

  history.push(next);
  state = next.after;

  selected = null;
  pendingPromotion = null;
  claimedDraw = "";

  renderMove(next.move, { captureIndex: next.captureIndex });
});

document.getElementById("flip-board").addEventListener("click", () => {
  flipped = !flipped;
  selected = null;

  render();
});

document.getElementById("toggle-view").addEventListener("click", event => {
  is3D = !is3D;

  ui.stage.classList.toggle("flat", !is3D);

  event.currentTarget.setAttribute(
    "aria-pressed",
    String(is3D)
  );

  event.currentTarget.textContent =
    is3D ? "3D view: on" : "3D view: off";
});

ui.claim.addEventListener("click", () => {
  if (!claimReason) {
    return;
  }

  claimedDraw = claimReason;
  selected = null;

  render();
});

document.addEventListener("keydown", event => {
  if (
    event.key === "Escape" &&
    !ui.promotion.open &&
    selected !== null
  ) {
    selected = null;
    render();
  }
});

/* ---------- Start ---------- */

render();
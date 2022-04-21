import { Queue } from "@datastructures-js/queue";
import { examples, registry } from "@penrose/examples";
import {
  constOf,
  debug,
  energyAndGradCompiled,
  markInput,
  varOf,
} from "engine/Autodiff";
import {
  absVal,
  acos,
  acosh,
  add,
  addN,
  and,
  asin,
  asinh,
  atan,
  atan2,
  atanh,
  cbrt,
  ceil,
  cos,
  cosh,
  div,
  eq,
  exp,
  expm1,
  floor,
  gt,
  ifCond,
  inverse,
  ln,
  log10,
  log1p,
  log2,
  lt,
  max,
  maxN,
  min,
  minN,
  mul,
  neg,
  or,
  pow,
  round,
  sign,
  sin,
  sinh,
  sqrt,
  squared,
  sub,
  tan,
  tanh,
  trunc,
} from "engine/AutodiffFunctions";
import * as fs from "fs";
import * as graphlib from "graphlib";
import { compileTrio, prepareState, showError } from "index";
import { VarAD } from "types/ad";
import { safe } from "utils/Util";

type Node =
  | ConstNode
  | InputNode
  | UnaryNode
  | BinaryNode
  | TernaryNode
  | NaryNode
  | DebugNode;

type ConstNode = number;

interface InputNode {
  tag: "Input";
  index: number;
  val: number;
}

interface UnaryNode {
  tag: "Unary";
  unop:
    | "neg"
    | "squared"
    | "sqrt"
    | "inverse"
    | "abs"
    | "acosh"
    | "acos"
    | "asin"
    | "asinh"
    | "atan"
    | "atanh"
    | "cbrt"
    | "ceil"
    | "cos"
    | "cosh"
    | "exp"
    | "expm1"
    | "floor"
    | "log"
    | "log2"
    | "log10"
    | "log1p"
    | "round"
    | "sign"
    | "sin"
    | "sinh"
    | "tan"
    | "tanh"
    | "trunc";
}

interface BinaryNode {
  tag: "Binary";
  binop:
    | "+"
    | "*"
    | "-"
    | "/"
    | "max"
    | "min"
    | "atan2"
    | "pow"
    | ">"
    | "<"
    | "==="
    | "&&"
    | "||";
}

interface TernaryNode {
  tag: "Ternary";
}

interface NaryNode {
  tag: "Nary";
  op: "addN" | "maxN" | "minN";
}

interface DebugNode {
  tag: "Debug";
  info: string;
}

type Edge = UnaryEdge | BinaryEdge | TernaryEdge | NaryEdge | DebugEdge;
type UnaryEdge = undefined;
type BinaryEdge = "left" | "right";
type TernaryEdge = "cond" | "then" | "els";
type NaryEdge = `${number}`;
type DebugEdge = undefined;

type Id = `_${number}`;

const indexToID = (index: number): Id => `_${index}`;

const indexToNaryEdge = (index: number): NaryEdge => `${index}`;
const naryEdgeToIndex = (name: NaryEdge) => parseInt(name, 10);

interface Child {
  child: VarAD;
  name: Edge;
}

const translate = (v: VarAD): { node: Node; children: Child[] } => {
  const { val, op, isInput, childrenAD, index } = v;
  const naryChildren: Child[] = childrenAD.map(({ node }, i) => ({
    child: node,
    name: indexToNaryEdge(i),
  }));
  if (op === "max list") {
    return { node: { tag: "Nary", op: "maxN" }, children: naryChildren };
  } else if (op === "min list") {
    return { node: { tag: "Nary", op: "minN" }, children: naryChildren };
  } else if (op === "+ list") {
    return { node: { tag: "Nary", op: "addN" }, children: naryChildren };
  } else if (childrenAD.length === 0) {
    if (isInput) {
      return { node: { tag: "Input", index: index + 1, val }, children: [] };
    } else {
      throw Error(":( #1");
    }
  } else if (childrenAD.length === 1) {
    const [{ node: child }] = childrenAD;
    const children = [{ child, name: undefined }];
    if (
      op === "squared" ||
      op === "cos" ||
      op === "sin" ||
      op === "sqrt" ||
      op === "abs"
    ) {
      return { node: { tag: "Unary", unop: op }, children };
    } else if (op === "- (unary)") {
      return { node: { tag: "Unary", unop: "neg" }, children };
    } else {
      throw Error(":( #2");
    }
  } else if (childrenAD.length === 2) {
    const [{ node: left }, { node: right }] = childrenAD;
    const children: Child[] = [
      { child: left, name: "left" },
      { child: right, name: "right" },
    ];
    if (
      op === "+" ||
      op === "*" ||
      op === "-" ||
      op === "max" ||
      op === "/" ||
      op === "min"
    ) {
      return { node: { tag: "Binary", binop: op }, children };
    } else if (op === "lt") {
      return { node: { tag: "Binary", binop: "<" }, children };
    } else {
      throw Error(":( #3");
    }
  } else if (childrenAD.length === 3) {
    const [{ node: cond }, { node: then }, { node: els }] = childrenAD;
    if (op === "ifCond") {
      return {
        node: { tag: "Ternary" },
        children: [
          { child: cond, name: "cond" },
          { child: then, name: "then" },
          { child: els, name: "els" },
        ],
      };
    } else {
      throw Error(":( #4");
    }
  } else {
    throw Error(":( #5");
  }
};

const stringifyGraph = (
  primary: Id,
  nodes: [Id, Node][],
  edges: { v: Id; w: Id; name?: Edge }[]
): string => {
  const [id0, node0] = nodes[0];
  const strings = [
    `{\n  "primary": ${JSON.stringify(
      primary
    )},\n  "nodes": {\n    ${JSON.stringify(id0)}: ${JSON.stringify(node0)}`,
  ];
  for (const [id, node] of nodes.slice(1)) {
    strings.push(`,\n    ${JSON.stringify(id)}: ${JSON.stringify(node)}`);
  }

  strings.push(`\n  },\n  "edges": [\n    ${JSON.stringify(edges[0])}`);
  for (const edge of edges.slice(1)) {
    strings.push(`,\n    ${JSON.stringify(edge)}`);
  }
  strings.push("\n  ]\n}\n");

  return strings.join("");
};

const fuzz = async (): Promise<void> => {
  const setTheory = examples["set-theory-domain"];
  const dslSet = setTheory["setTheory.dsl"];
  const styVenn = setTheory["venn.sty"];
  const subTree = setTheory["tree.sub"];
  const variation = safe(
    registry.trios.find(
      ({ substance, style }) => substance === "tree" && style === "venn"
    ),
    "tree-venn should exist"
  ).variation;

  const res = compileTrio({
    substance: subTree,
    style: styVenn,
    domain: dslSet,
    variation,
  });
  if (!res.isOk()) {
    throw Error(showError(res.error));
  }

  // resample because initial sampling did not use the special sampling seed
  const { params } = await prepareState(res.value);

  const constants = new Map<number, Id>();
  const ids = new Map<VarAD, Id>();
  const nodes = new Map<Id, Node>();
  const queue = new Queue([params.energyGraph]);
  const edges: [Child, VarAD][] = [];
  while (!queue.isEmpty()) {
    const v = queue.dequeue();
    if (!v.op.endsWith(" list") && v.childrenAD.length === 0 && !v.isInput) {
      let id = constants.get(v.val);
      if (id === undefined) {
        id = indexToID(nodes.size);
        constants.set(v.val, id);
        nodes.set(id, v.val);
      }
      ids.set(v, id);
    } else if (!ids.has(v)) {
      const id = indexToID(nodes.size);
      ids.set(v, id);
      const { node, children } = translate(v);
      nodes.set(id, node);
      for (const edge of children) {
        edges.push([edge, v]);
        queue.enqueue(edge.child);
      }
    }
  }

  fs.writeFileSync(
    "graph.json",
    stringifyGraph(
      safe(ids.get(params.energyGraph), ":( #6"),
      [...nodes.entries()],
      edges.map(([{ child, name }, parent]) => ({
        v: safe(ids.get(child), ":( #7"),
        w: safe(ids.get(parent), ":( #8"),
        name,
      }))
    ),
    "utf8"
  );

  const secondary = [];
  for (const [{ val }, id] of ids) {
    secondary.push([id, val]);
  }
  fs.writeFileSync(
    "outputs.json",
    `${JSON.stringify(
      {
        gradient: params.currGradient(params.xsVars.map(({ val }) => val)),
        primary: params.energyGraph.val,
        secondary: Object.fromEntries(secondary),
      },
      null,
      2
    )}\n`,
    "utf8"
  );
};

const getGraph = (
  filename = "graph.json"
): { primary: Id; graph: graphlib.Graph } => {
  const graph = new graphlib.Graph({ multigraph: true });
  const { primary, nodes, edges } = JSON.parse(
    fs.readFileSync(filename, "utf8")
  );
  for (const [id, node] of Object.entries(nodes)) {
    graph.setNode(id, node);
  }
  for (const { v, w, name } of edges) {
    graph.setEdge(v, w, undefined, name);
  }
  return { primary, graph };
};

const translateUnary = ({ unop }: UnaryNode): ((param: VarAD) => VarAD) => {
  switch (unop) {
    case "neg": {
      return neg;
    }
    case "squared": {
      return squared;
    }
    case "inverse": {
      return inverse;
    }
    case "sqrt": {
      return sqrt;
    }
    case "abs": {
      return absVal;
    }
    case "acosh": {
      return acosh;
    }
    case "acos": {
      return acos;
    }
    case "asin": {
      return asin;
    }
    case "asinh": {
      return asinh;
    }
    case "atan": {
      return atan;
    }
    case "atanh": {
      return atanh;
    }
    case "cbrt": {
      return cbrt;
    }
    case "ceil": {
      return ceil;
    }
    case "cos": {
      return cos;
    }
    case "cosh": {
      return cosh;
    }
    case "exp": {
      return exp;
    }
    case "expm1": {
      return expm1;
    }
    case "floor": {
      return floor;
    }
    case "log": {
      return ln;
    }
    case "log2": {
      return log2;
    }
    case "log10": {
      return log10;
    }
    case "log1p": {
      return log1p;
    }
    case "round": {
      return round;
    }
    case "sign": {
      return sign;
    }
    case "sin": {
      return sin;
    }
    case "sinh": {
      return sinh;
    }
    case "tan": {
      return tan;
    }
    case "tanh": {
      return tanh;
    }
    case "trunc": {
      return trunc;
    }
  }
};

const translateBinary = ({
  binop,
}: BinaryNode): ((left: VarAD, right: VarAD) => VarAD) => {
  switch (binop) {
    case "+": {
      return add;
    }
    case "*": {
      return mul;
    }
    case "-": {
      return sub;
    }
    case "/": {
      return div;
    }
    case ">": {
      return gt;
    }
    case "<": {
      return lt;
    }
    case "===": {
      return eq;
    }
    case "&&": {
      return and;
    }
    case "||": {
      return or;
    }
    case "max": {
      return max;
    }
    case "min": {
      return min;
    }
    case "atan2": {
      return atan2;
    }
    case "pow": {
      return pow;
    }
  }
};

const translateNary = ({ op }: NaryNode): ((params: VarAD[]) => VarAD) => {
  switch (op) {
    case "addN": {
      return addN;
    }
    case "maxN": {
      return maxN;
    }
    case "minN": {
      return minN;
    }
  }
};

const translateBack = (node: Node, children: Map<Edge, VarAD>): VarAD => {
  if (typeof node === "number") {
    return constOf(node);
  }
  switch (node.tag) {
    case "Input": {
      return markInput(varOf(node.val), node.index);
    }
    case "Unary": {
      return translateUnary(node)(safe(children.get(undefined), ":( #9"));
    }
    case "Binary": {
      return translateBinary(node)(
        safe(children.get("left"), ":( #10"),
        safe(children.get("right"), ":( #11")
      );
    }
    case "Ternary": {
      return ifCond(
        safe(children.get("cond"), ":( #12"),
        safe(children.get("then"), ":( #13"),
        safe(children.get("els"), ":( #14")
      );
    }
    case "Nary": {
      const params: VarAD[] = [];
      for (const [i, v] of children) {
        params[naryEdgeToIndex(i as NaryEdge)] = v;
      }
      return translateNary(node)(params);
    }
    case "Debug": {
      return debug(safe(children.get(undefined), ":( #15"));
    }
  }
};

const gradients = (): void => {
  const { graph } = getGraph();
  const sorted = graphlib.alg.topsort(graph);
  for (const primary of graph.nodes()) {
    const reachable = new Set<string>();
    const queue = new Queue([primary]);
    while (!queue.isEmpty()) {
      const id = queue.dequeue();
      if (!reachable.has(id)) {
        reachable.add(id);
        const preds = graph.predecessors(id);
        if (!Array.isArray(preds)) {
          throw Error(":( #16");
        }
        for (const pred of preds) {
          queue.enqueue(pred);
        }
      }
    }

    const varADs = new Map<string, VarAD>();
    const xsVars = [];
    for (const id of sorted) {
      const node: Node = graph.node(id);
      if (
        !(
          reachable.has(id) ||
          (typeof node !== "number" && node.tag === "Input")
        )
      ) {
        continue;
      }
      const edges = graph.inEdges(id);
      if (!Array.isArray(edges)) {
        throw Error(":( #17");
      }
      const v = translateBack(
        node,
        new Map(
          edges.map(({ v, name }) => [
            name as Edge,
            safe(varADs.get(v), ":( #18"),
          ])
        )
      );
      varADs.set(id, v);
      if (v.isInput) {
        xsVars[v.index] = v;
      }
    }

    const xs = xsVars.map(({ val }) => val);
    const energyGraph = safe(varADs.get(primary), ":( #19");
    if (energyGraph.isInput) {
      continue;
    }
    const { f, gradf } = energyAndGradCompiled(
      xs,
      xsVars,
      energyGraph,
      undefined
    );

    fs.writeFileSync(
      `outputs/${primary}.json`,
      `${JSON.stringify({ gradient: gradf(xs), primary: f(xs) }, null, 2)}\n`
    );
  }
};

const shrunk = (): void => {
  const { graph } = getGraph("graph_1396_shrunk.json");
  const varADs = new Map<string, VarAD>();
  const xsVars = [];
  for (const id of graphlib.alg.topsort(graph)) {
    const node: Node = graph.node(id);
    const edges = graph.inEdges(id);
    if (!Array.isArray(edges)) {
      throw Error(":( #20");
    }
    const v = translateBack(
      node,
      new Map(
        edges.map(({ v, name }) => [
          name as Edge,
          safe(varADs.get(v), ":( #21"),
        ])
      )
    );
    varADs.set(id, v);
    if (v.isInput) {
      xsVars[v.index] = v;
    }
  }

  const xs = xsVars.map(({ val }) => val);
  const energyGraph = safe(varADs.get("_0"), ":( #22");
  const { f, gradf } = energyAndGradCompiled(
    xs,
    xsVars,
    energyGraph,
    undefined
  );

  fs.writeFileSync(
    `output_1396_shrunk.json`,
    `${JSON.stringify({ gradient: gradf(xs), primary: f(xs) }, null, 2)}\n`
  );
};

const genSqrt = (): void => {
  const x0 = markInput(varOf(0), 0);
  const { progInputs, progStr } = energyAndGradCompiled(
    [0],
    [x0],
    sqrt(x0),
    undefined
  );
  fs.writeFileSync(
    "sqrt.js",
    `(${progInputs.join(", ")}) => {\n  ${progStr
      .split("\n")
      .join("\n  ")}\n}\n`
  );
};

export const main = genSqrt;

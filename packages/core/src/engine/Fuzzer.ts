import { Queue } from "@datastructures-js/queue";
import { examples, registry } from "@penrose/examples";
import {
  EPS_DENOM,
  genCode,
  makeGraph,
  primaryGraph,
  secondaryGraph,
} from "engine/Autodiff";
import * as fs from "fs";
import * as graphlib from "graphlib";
import { compileTrio, prepareState, resample, showError } from "index";
import * as ad from "types/ad";
import { VarAD } from "types/ad";
import { safe } from "utils/Util";

const stringifyNode = (node: ad.Node, inputs: number[]): string => {
  let obj: any = node;
  if (typeof node !== "number" && node.tag === "Input") {
    obj = { ...obj, val: inputs[node.index] };
  }
  return JSON.stringify(obj);
};

const stringifyGraph = (
  { graph, primary }: ad.Graph,
  inputs: number[]
): string => {
  const [node0, ...nodes] = graph.nodes();
  const strings = [
    `{\n  "primary": ${JSON.stringify(
      primary
    )},\n  "nodes": {\n    ${JSON.stringify(node0)}: ${stringifyNode(
      graph.node(node0),
      inputs
    )}`,
  ];
  for (const id of nodes) {
    strings.push(
      `,\n    ${JSON.stringify(id)}: ${stringifyNode(graph.node(id), inputs)}`
    );
  }

  const [edge0, ...edges] = graph.edges();
  strings.push(`\n  },\n  "edges": [\n    ${JSON.stringify(edge0)}`);
  for (const edge of edges) {
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
  const {
    params: { energyGraph },
  } = resample(await prepareState(res.value));

  const g1 = secondaryGraph([energyGraph]);
  const pairs = [...g1.nodes.entries()];

  const inputs = [];
  for (const [v] of pairs) {
    if (typeof v !== "number" && v.tag === "Input") {
      inputs[v.index] = v.val;
    }
  }

  fs.writeFileSync(
    "graph.json",
    stringifyGraph(
      { ...g1, primary: safe(g1.nodes.get(energyGraph), ":(") },
      inputs
    ),
    "utf8"
  );

  const g2 = makeGraph({
    primary: energyGraph,
    secondary: pairs.map(([v]) => v),
  });
  const f = genCode(g2);

  const outputs = f(inputs);

  const secondary = Object.fromEntries(
    pairs.map(([, id], i) => {
      const x = outputs.secondary[i];
      return [id, typeof x === "boolean" ? (x ? 1 : 0) : x];
    })
  );
  fs.writeFileSync(
    "outputs.json",
    `${JSON.stringify(
      {
        gradient: outputs.gradient.slice(1),
        primary: outputs.primary,
        secondary,
      },
      null,
      2
    )}\n`,
    "utf8"
  );
};

const getGraph = (filename = "graph.json"): graphlib.Graph => {
  const graph = new graphlib.Graph({ multigraph: true });
  const { nodes, edges } = JSON.parse(fs.readFileSync(filename, "utf8"));
  for (const [id, node] of Object.entries(nodes)) {
    graph.setNode(id, node);
  }
  for (const { v, w, name } of edges) {
    graph.setEdge(v, w, undefined, name);
  }
  return graph;
};

const layers = (): void => {
  const graph = getGraph();

  const depths = new Map<string, number>();
  const queue = new Queue<{ id: string; depth: number }>();
  for (const id of graph.sources()) {
    queue.enqueue({ id, depth: 0 });
  }
  while (!queue.isEmpty()) {
    const { id, depth } = queue.dequeue();
    depths.set(id, depth);
    const parents = graph.successors(id);
    if (!Array.isArray(parents)) {
      throw Error(":(");
    }
    parents: for (const parent of parents) {
      if (!depths.has(parent)) {
        const siblings = graph.predecessors(parent);
        if (!Array.isArray(siblings)) {
          throw Error(":(");
        }
        const siblingDepths = [];
        for (const sibling of siblings) {
          const siblingDepth = depths.get(sibling);
          if (siblingDepth === undefined) {
            continue parents;
          } else {
            siblingDepths.push(siblingDepth);
          }
        }
        queue.enqueue({ id: parent, depth: Math.max(...siblingDepths) + 1 });
      }
    }
  }

  const layers: string[][] = [];
  for (const [id, depth] of depths) {
    if (!(depth in layers)) {
      layers[depth] = [];
    }
    layers[depth].push(id);
  }
  fs.writeFileSync(
    "layers.json",
    `${JSON.stringify(layers, null, 2)}\n`,
    "utf8"
  );
};

const naryEdgeToIndex = (name: ad.NaryEdge) => parseInt(name, 10);

const translate = (node: ad.Node, children: Map<ad.Edge, VarAD>): VarAD => {
  if (typeof node === "number") {
    return node;
  }
  const { tag } = node;
  switch (tag) {
    case "Input": {
      const { index, val } = node as ad.Input; // HACK
      return { tag, index, val };
    }
    case "Unary": {
      const { unop } = node;
      const param = safe(children.get(undefined), ":(");
      if (typeof param === "number") {
        if (unop === "neg") {
          return -param;
        } else if (unop === "squared") {
          return param * param;
        } else if (unop === "inverse") {
          return 1 / (param + EPS_DENOM);
        } else {
          return Math[unop](param);
        }
      }
      return { tag, unop, param };
    }
    case "Binary": {
      const { binop } = node;
      const left = safe(children.get("left"), ":(");
      const right = safe(children.get("right"), ":(");
      if (typeof left === "number" && typeof right === "number") {
        if (binop === "+") {
          return left + right;
        } else if (binop === "*") {
          return left * right;
        } else if (binop === "-") {
          return left - right;
        } else if (binop === "/") {
          return left / right;
        } else if (binop === "max") {
          return Math.max(left, right);
        } else if (binop === "min") {
          return Math.min(left, right);
        } else if (binop === "atan2") {
          return Math.atan2(left, right);
        } else if (binop === "pow") {
          return Math.pow(left, right);
        }
      }
      return { tag, binop, left, right };
    }
    case "Ternary": {
      return {
        tag,
        cond: safe(children.get("cond"), ":("),
        then: safe(children.get("then"), ":("),
        els: safe(children.get("els"), ":("),
      };
    }
    case "Nary": {
      const { op } = node;
      const params: VarAD[] = [];
      for (const [i, v] of children) {
        params[naryEdgeToIndex(i as ad.NaryEdge)] = v;
      }
      return { tag, op, params };
    }
    case "Debug": {
      const { info } = node;
      return { tag, info, node: safe(children.get(undefined), ":(") };
    }
  }
};

const translateAll = (
  graph: graphlib.Graph
): { varADs: Map<string, VarAD>; inputs: number[] } => {
  const varADs = new Map<string, VarAD>();
  const inputs = [];
  for (const id of graphlib.alg.topsort(graph)) {
    const edges = graph.inEdges(id);
    if (!Array.isArray(edges)) {
      throw Error(":(");
    }
    const v = translate(
      graph.node(id),
      new Map(
        edges.map(({ v, name }) => [name as ad.Edge, safe(varADs.get(v), ":(")])
      )
    );
    varADs.set(id, v);
    if (typeof v !== "number" && v.tag === "Input") {
      inputs[v.index] = v.val;
    }
  }
  return { varADs, inputs };
};

const gradients = (): void => {
  const graph = getGraph();
  const { varADs, inputs } = translateAll(graph);
  for (const [id, v] of varADs) {
    const g = primaryGraph(v);
    const f = genCode(g);
    const { primary, gradient } = f(inputs);
    fs.writeFileSync(
      `outputs/${id}.json`,
      `${JSON.stringify(
        {
          gradient: inputs.map((x, i) => (i in gradient ? gradient[i] : 0)),
          primary,
        },
        null,
        2
      )}\n`
    );
  }
};

// git checkout delta-main -- outputs/
// git status --porcelain
const different = new Set([
  "_0",
  "_1010",
  "_11",
  "_113",
  "_1159",
  "_1243",
  "_1322",
  "_1396",
  "_150",
  "_1606",
  "_1630",
  "_1658",
  "_1687",
  "_195",
  "_2",
  "_22",
  "_237",
  "_280",
  "_327",
  "_34",
  "_381",
  "_435",
  "_49",
  "_5",
  "_500",
  "_565",
  "_630",
  "_66",
  "_696",
  "_763",
  "_827",
  "_86",
  "_889",
  "_946",
]);

const rank = (): void => {
  const layers: string[][] = JSON.parse(fs.readFileSync("layers.json", "utf8"));
  const ranks: { [layer: number]: string[] } = {};
  layers.forEach((layer, i) => {
    const filtered = layer.filter((id) => different.has(id));
    if (filtered.length > 0) {
      ranks[i] = filtered;
    }
  });
  console.log(ranks);
};

const pprintNode = (node: ad.Node): string => {
  if (typeof node === "number") {
    return `${node}`;
  }
  switch (node.tag) {
    case "Input": {
      return `i${node.index}`;
    }
    case "Unary": {
      return node.unop;
    }
    case "Binary": {
      return node.binop;
    }
    case "Ternary": {
      return "?:";
    }
    case "Nary": {
      return node.op;
    }
    case "Debug": {
      return `d${JSON.stringify(node.info)}`;
    }
  }
};

const noncommutative = new Set<ad.BinaryNode["binop"]>([
  "-",
  "/",
  "atan2",
  "pow",
  ">",
  "<",
]);

const pprintGraph = (graph: graphlib.Graph): string => {
  const lines = ["digraph {"];
  for (const id of graph.nodes()) {
    lines.push(`  ${id} [label = "${pprintNode(graph.node(id))}"];`);
  }
  for (const { v, w, name } of graph.edges()) {
    const node = graph.node(w);
    if (
      name !== undefined &&
      typeof node !== "number" &&
      node.tag === "Binary" &&
      noncommutative.has(node.binop)
    ) {
      lines.push(`  ${v} -> ${w} [label = "${name[0]}"];`);
    } else {
      lines.push(`  ${v} -> ${w};`);
    }
  }
  lines.push("}", "");
  return lines.join("\n");
};

const pprint = (): void => {
  const graph = getGraph();
  const { varADs } = translateAll(graph);
  const primary = "_1396";
  const g = secondaryGraph([safe(varADs.get(primary), ":(")]);
  fs.writeFileSync(`graph${primary}.gv`, pprintGraph(g.graph), "utf8");
};

const shrink = (): void => {
  const graph = getGraph("graph_1396.json");
  for (const id of graph.sources()) {
    const node: ad.Node = graph.node(id);
    if (typeof node !== "number" && node.tag === "Input") {
      if (node.index === 30) {
        node.index = 0;
      } else {
        graph.setNode(id, (node as ad.Input).val); // HACK
      }
    }
  }
  const { varADs, inputs } = translateAll(graph);
  const primaryVar = safe(varADs.get("_0"), ":(");

  const g2 = secondaryGraph([primaryVar]);
  fs.writeFileSync("graph_1396_shrunk.json", stringifyGraph(g2, inputs));
  fs.writeFileSync(`graph_1396_shrunk.gv`, pprintGraph(g2.graph), "utf8");

  const g = primaryGraph(primaryVar);
  const f = genCode(g);
  const { primary, gradient } = f(inputs);
  fs.writeFileSync(
    "output_1396_shrunk.json",
    `${JSON.stringify(
      {
        gradient: inputs.map((x, i) => (i in gradient ? gradient[i] : 0)),
        primary,
      },
      null,
      2
    )}\n`
  );
};

const genShrunk = (): void => {
  const graph = getGraph("graph_1396_shrunk.json");
  const { varADs, inputs } = translateAll(graph);
  const primary = safe(varADs.get("_0"), ":(");
  fs.writeFileSync(
    "graph_1396_shrunk.js",
    `const f = ${
      genCode(primaryGraph(primary))([0]).code
    }\nconsole.log(f(${JSON.stringify(inputs)}));\n`
  );
};

export const main = genShrunk;

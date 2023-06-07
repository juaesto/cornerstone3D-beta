export class UnionFind {
  roots: number[];
  ranks: number[];

  constructor(count: number) {
    this.roots = new Array<number>(count);
    this.ranks = new Array<number>(count);

    for (let i = 0; i < count; ++i) {
      this.roots[i] = i;
      this.ranks[i] = 0;
    }
  }

  public makeSet() {
    const n = this.roots.length;
    this.roots.push(n);
    this.ranks.push(0);
    return n;
  }

  public find(x) {
    let x0 = x;
    const roots = this.roots;
    while (roots[x] !== x) {
      x = roots[x];
    }
    while (roots[x0] !== x) {
      const y = roots[x0];
      roots[x0] = x;
      x0 = y;
    }
    return x;
  }

  public link(x, y) {
    const xr = this.find(x),
      yr = this.find(y);
    if (xr === yr) {
      return;
    }
    const ranks = this.ranks,
      roots = this.roots,
      xd = ranks[xr],
      yd = ranks[yr];
    if (xd < yd) {
      roots[xr] = yr;
    } else if (yd < xd) {
      roots[yr] = xr;
    } else {
      roots[yr] = xr;
      ++ranks[xr];
    }
  }
}

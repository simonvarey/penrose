(x0) => {
  const x1 = 2;
  const x2 = x1 * x0;
  const x3 = 1;
  const x4 = 1;
  const x5 = 2;
  const x6 = 0.00001;
  const x7 = x0 * x0;
  const x8 = x0 * x0;
  const x9 = x7 + x8;
  const x10 = Math.sqrt(x9);
  const x11 = Math.max(x6, x10);
  const x12 = x5 * x11;
  const x13 = x4 / x12;
  const x14 = 1;
  const x15 = x13 * x14;
  const x16 = x3 * x15;
  const x17 = x2 * x16;
  const x18 = 1;
  const x19 = x18 * x15;
  const x20 = x0 * x19;
  const x21 = x0 * x19;
  const x22 = [x17, x20, x21].reduce((x, y) => x + y);
  return [x22];
}

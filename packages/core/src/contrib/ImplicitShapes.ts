import { outwardUnitNormal } from "contrib/Queries";
import { ops } from "engine/Autodiff";
import { add, div, mul, neg, squared, sub } from "engine/AutodiffFunctions";
import { Circle } from "shapes/Circle";
import { Ellipse } from "shapes/Ellipse";
import * as ad from "types/ad";
import { numsOf } from "./Utils";

/**
 * Parameters of implicitly defined ellipse:
 * `a * (X - x)^2 + b * (Y - y)^2 = c`
 */
export interface ImplicitEllipse {
  a: ad.Num;
  b: ad.Num;
  c: ad.Num;
  x: ad.Num;
  y: ad.Num;
}

/**
 * Parameters of implicitly defined half-plane:
 * `a * X + b * Y <= c`
 */
export interface ImplicitHalfPlane {
  a: ad.Num;
  b: ad.Num;
  c: ad.Num;
}

/**
 * Evaluate the implicit function for an ellipse at point with coordinates `x` and `y`.
 * @param ei Implicit ellipse parameters.
 * @param x X-coordinate.
 * @param y Y-coordinate.
 */
export const implicitEllipseFunc = (
  ei: ImplicitEllipse,
  x: ad.Num,
  y: ad.Num
): ad.Num => {
  return sub(
    add(mul(ei.a, squared(sub(x, ei.x))), mul(ei.b, squared(sub(y, ei.y)))),
    ei.c
  );
};

/**
 * Evaluate the implicit function for an half-plane at point with coordinates `x` and `y`.
 * @param hpi Implicit half-plane parameters.
 * @param x X-coordinate.
 * @param y Y-coordinate.
 */
export const implicitHalfPlaneFunc = (
  hpi: ImplicitHalfPlane,
  x: ad.Num,
  y: ad.Num
): ad.Num => {
  return sub(add(mul(hpi.a, x), mul(hpi.b, y)), hpi.c);
};

/**
 * Return implicit half-plane parameters given a line and a point inside the half-plane.
 * @param lineSegment Two points defining the line segment.
 * @param insidePoint Any point inside of the half-plane.
 * @param padding Padding around the Half-plane.
 */
export const halfPlaneToImplicit = (
  lineSegment: ad.Num[][],
  insidePoint: ad.Num[],
  padding: ad.Num
): ImplicitHalfPlane => {
  const normal = outwardUnitNormal(lineSegment, insidePoint);
  return {
    a: normal[0],
    b: normal[1],
    c: sub(ops.vdot(normal, lineSegment[0]), padding),
  };
};

/**
 * Return implicit ellipse parameters from an explicit representation.
 * @param ellipse Explicit ellipse shape.
 */
export const ellipseToImplicit = (
  ellipse: Ellipse,
  padding: ad.Num
): ImplicitEllipse => {
  const rx = add(ellipse.rx.contents, padding);
  const ry = add(ellipse.ry.contents, padding);
  return {
    a: div(ry, rx),
    b: div(rx, ry),
    c: mul(rx, ry),
    x: ellipse.center.contents[0],
    y: ellipse.center.contents[1],
  };
};

/**
 * Return implicit ellipse parameters from an explicit circle.
 * @param circle Explicit circle shape.
 */
export const circleToImplicitEllipse = (
  circle: Circle,
  padding: ad.Num
): ImplicitEllipse => {
  return {
    a: 1,
    b: 1,
    c: squared(add(circle.r.contents, padding)),
    x: circle.center.contents[0],
    y: circle.center.contents[1],
  };
};

// Constant coefficient from the ellipse-ellipse polynomial
const ellipsePolynomailAlpha0 = (
  a: ImplicitEllipse,
  b: ImplicitEllipse
): ad.Num => {
  return mul(
    mul(squared(a.a), squared(a.b)),
    add(
      sub(a.c, b.c),
      add(mul(b.a, squared(sub(b.x, a.x))), mul(b.b, squared(sub(b.y, a.y))))
    )
  );
};

// Linear coefficient from the ellipse-ellipse polynomial
const ellipsePolynomailAlpha1 = (
  a: ImplicitEllipse,
  b: ImplicitEllipse
): ad.Num => {
  const coef = mul(2, mul(a.a, a.b));
  return mul(
    coef,
    add(
      mul(sub(a.c, b.c), sub(add(mul(a.a, b.b), mul(a.b, b.a)), coef)),
      add(
        mul(mul(a.a, b.a), mul(squared(sub(b.x, a.x)), sub(b.b, mul(2, a.b)))),
        mul(mul(a.b, b.b), mul(squared(sub(b.y, a.y)), sub(b.a, mul(2, a.a))))
      )
    )
  );
};

// Quadratic coefficient from the ellipse-ellipse polynomial
const ellipsePolynomailAlpha2 = (
  a: ImplicitEllipse,
  b: ImplicitEllipse
): ad.Num => {
  const coeff1 = add(
    add(
      mul(squared(a.a), squared(sub(b.b, a.b))),
      mul(squared(a.b), squared(sub(b.a, a.a)))
    ),
    mul(mul(4, mul(a.a, a.b)), mul(sub(b.b, a.b), sub(b.a, a.a)))
  );
  const coeff2 = sub(
    mul(squared(a.b), sub(mul(6, a.a), b.a)),
    mul(mul(a.a, b.b), sub(mul(6, a.b), b.b))
  );
  const coeff3 = sub(
    mul(squared(a.a), sub(mul(6, a.b), b.b)),
    mul(mul(a.b, b.a), sub(mul(6, a.a), b.a))
  );
  return add(
    mul(coeff1, sub(a.c, b.c)),
    add(
      mul(mul(coeff2, mul(a.a, b.a)), squared(sub(b.x, a.x))),
      mul(mul(coeff3, mul(a.b, b.b)), squared(sub(b.y, a.y)))
    )
  );
};

// Cubic coefficient from the ellipse-ellipse polynomial
const ellipsePolynomailAlpha3 = (
  a: ImplicitEllipse,
  b: ImplicitEllipse
): ad.Num => {
  const factor = mul(
    2,
    sub(mul(2, mul(a.a, a.b)), add(mul(a.b, b.a), mul(a.a, b.b)))
  );
  return mul(
    factor,
    add(
      mul(mul(sub(b.a, a.a), sub(b.b, a.b)), sub(b.c, a.c)),
      add(
        mul(mul(a.a, b.a), mul(squared(sub(b.x, a.x)), sub(b.b, a.b))),
        mul(mul(a.b, b.b), mul(squared(sub(b.y, a.y)), sub(b.a, a.a)))
      )
    )
  );
};

// Quintic coefficient from the ellipse-ellipse polynomial
const ellipsePolynomailAlpha4 = (
  a: ImplicitEllipse,
  b: ImplicitEllipse
): ad.Num => {
  return neg(
    add(
      mul(mul(squared(sub(b.a, a.a)), squared(sub(b.b, a.b))), sub(b.c, a.c)),
      add(
        mul(
          mul(mul(a.a, b.a), squared(sub(b.x, a.x))),
          mul(sub(b.a, a.a), squared(sub(b.b, a.b)))
        ),
        mul(
          mul(mul(a.b, b.b), squared(sub(b.y, a.y))),
          mul(squared(sub(b.a, a.a)), sub(b.b, a.b))
        )
      )
    )
  );
};

// Coefficients of the ellipse-ellipse polynomial
// (ordered from the lowest by their corresponding deggree)
const ellipsePolynomialParams = (
  a: ImplicitEllipse,
  b: ImplicitEllipse
): ad.Num[] => {
  return [
    ellipsePolynomailAlpha0(a, b),
    ellipsePolynomailAlpha1(a, b),
    ellipsePolynomailAlpha2(a, b),
    ellipsePolynomailAlpha3(a, b),
    ellipsePolynomailAlpha4(a, b),
  ];
};

// Return order of a polynomial given by its coefficients
// (ordered from the lowest by their corresponding deggree)
export const polyOrder = (poly: number[]): number => {
  for (let i = poly.length - 1; i > 0; i--) {
    if (poly[i] !== 0) return i;
  }
  return 0;
};

// Return monic polynomial coefficients
// (the highest order coefficient is ommited and assumed to be 1)
export const ellipsePolynomial = (
  a: ImplicitEllipse,
  b: ImplicitEllipse
): ad.Num[] => {
  const params = ellipsePolynomialParams(a, b);
  const order = polyOrder(numsOf(params));
  return Array.from(Array(order).keys()).map((i) =>
    div(params[i], params[order])
  );
};

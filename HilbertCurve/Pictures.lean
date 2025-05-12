import HilbertCurve.HilbertCurveNat
import ProofWidgets.Data.Svg
import ProofWidgets.Component.HtmlDisplay


open ProofWidgets Svg

private def frame : Frame where
  xmin   := -2
  ymin   := -2
  xSize  := 4
  width  := 400
  height := 400

/--
  Create an SVG visualization of the i-th order Hilbert curve.
-/
def hilbert_curve_svg (i : ℕ) : Svg frame :=
  let total_points := hilbert_length i
  let scale := (2^i : Nat).toFloat

  -- Generate all line segments
  let lineElements := (List.range (total_points - 1)).map (fun j =>
    let (x1, y1) := hilbert_curve i j
    let (x2, y2) := hilbert_curve i (j+1)

    -- Scale points to fit in the frame
    let p1 := (x1.toFloat / scale * 2 - 1, y1.toFloat / scale * 2 - 1)
    let p2 := (x2.toFloat / scale * 2 - 1, y2.toFloat / scale * 2 - 1)

    line p1 p2 |>.setStroke (0., 0., 1.) (.px 1))

  { elements := lineElements.toArray }

-- Example: Display a Hilbert curve of order 2
#html (hilbert_curve_svg 2).toHtml
#html (hilbert_curve_svg 2).toHtml -- Looks good

/--
  Create an SVG visualization of two Hilbert curves of different orders.
-/
def hilbert_curve_with_points (i : ℕ) : Svg frame :=
  let total_points := hilbert_length i
  let scale := (2^i : Nat).toFloat

  -- Generate all line segments
  let lineElements := (List.range (total_points - 1)).map (fun j =>
    let (x1, y1) := hilbert_curve i j
    let (x2, y2) := hilbert_curve i (j+1)

    -- Scale points to fit in the frame
    let p1 := (x1.toFloat / scale * 2 - 1, y1.toFloat / scale * 2 - 1)
    let p2 := (x2.toFloat / scale * 2 - 1, y2.toFloat / scale * 2 - 1)

    line p1 p2 |>.setStroke (0., 0., 1.) (.px 1))

  -- Generate points at each coordinate
  let pointElements := (List.range total_points).map (fun j =>
    let (x, y) := hilbert_curve i j
    -- Scale point to fit in the frame
    let p := (x.toFloat / scale * 2 - 1, y.toFloat / scale * 2 - 1)
    circle p (.abs 0.03) |>.setStroke (0.,0.,0.) (.px 1) |>.setFill (1.,0.,0.) |>.setId s!"point{j}")

  { elements := (lineElements ++ pointElements).toArray }

-- Example: Display a Hilbert curve of order 2 with points
#html (hilbert_curve_with_points 2).toHtml

def compare_hilbert_curves (i j : ℕ) : Svg frame :=
  let total_points_i := hilbert_length i
  let total_points_j := hilbert_length j
  let scale_i := (2^i : Nat).toFloat
  let scale_j := (2^j : Nat).toFloat

  -- Generate line segments for the first curve (red)
  let lineElements_i := (List.range (total_points_i - 1)).map (fun k =>
    let (x1, y1) := hilbert_curve i k
    let (x2, y2) := hilbert_curve i (k+1)
    let p1 := (x1.toFloat / scale_i * 2 - 1, y1.toFloat / scale_i * 2 - 1)
    let p2 := (x2.toFloat / scale_i * 2 - 1, y2.toFloat / scale_i * 2 - 1)
    line p1 p2 |>.setStroke (1., 0., 0.) (.px 4))

  -- Generate line segments for the second curve (blue)
  let lineElements_j := (List.range (total_points_j - 1)).map (fun k =>
    let (x1, y1) := hilbert_curve j k
    let (x2, y2) := hilbert_curve j (k+1)
    let p1 := (x1.toFloat / scale_j * 2 - 1, y1.toFloat / scale_j * 2 - 1)
    let p2 := (x2.toFloat / scale_j * 2 - 1, y2.toFloat / scale_j * 2 - 1)
    line p1 p2 |>.setStroke (0., 0., 1.) (.px 1))

  -- Generate points at each coordinate
  let pointElements_i := (List.range total_points_i).map (fun j =>
    let (x, y) := hilbert_curve i j
    -- Scale point to fit in the frame
    let p := (x.toFloat / scale_i * 2 - 1, y.toFloat / scale_i * 2 - 1)
    circle p (.abs 0.05) |>.setStroke (0.,0.,0.) (.px 2) |>.setFill (1.,0.,0.) |>.setId s!"point{j}")

  -- Generate points at each coordinate
  let pointElements_j := (List.range total_points_j).map (fun k =>
    let (x, y) := hilbert_curve j k
    -- Scale point to fit in the frame
    let p := (x.toFloat / scale_j * 2 - 1, y.toFloat / scale_j * 2 - 1)
    circle p (.abs 0.02) |>.setStroke (0.,0.,0.) (.px 1) |>.setFill (0.,1.,0.) |>.setId s!"point{k}")


  { elements := (lineElements_i ++ lineElements_j ++ pointElements_i ++ pointElements_j).toArray }

-- Example: Compare Hilbert curves of order 2 and 3
#html (compare_hilbert_curves 2 3).toHtml

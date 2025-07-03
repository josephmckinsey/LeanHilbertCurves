import HilbertCurve.HilbertCurveNat
import ProofWidgets.Data.Svg
import ProofWidgets.Component.HtmlDisplay
import ProofWidgets.Component.Recharts -- For Recharts components
-- Note: HilbertCurve.HilbertCurveNat, ProofWidgets.Data.Svg, ProofWidgets.Component.HtmlDisplay
-- are assumed to be imported from the existing code in the file.

namespace HilbertCurve

open ProofWidgets Svg

private def hueToRgb (p q t : Float) : Float :=
  let t' := if t < 0 then t + 1 else if t > 1 then t - 1 else t
  if t' < 1/6 then p + (q - p) * 6 * t'
  else if t' < 1/2 then q
  else if t' < 2/3 then p + (q - p) * (2/3 - t') * 6
  else p

private def hslToRgb (h s l : Float) : (Float × Float × Float) :=
  if s == 0 then (l, l, l) -- achromatic
  else
    let q := if l < 0.5 then l * (1 + s) else l + s - l * s
    let p := 2 * l - q
    let r := hueToRgb p q (h + 1/3)
    let g := hueToRgb p q h
    let b := hueToRgb p q (h - 1/3)
    (r, g, b)

private def frame : Frame where
  xmin   := -2
  ymin   := -2
  xSize  := 4
  width  := 400
  height := 400

/--
  Create an SVG visualization of the i-th order Hilbert curve.
-/
def hilbert_curve_svg (i : ℕ) (stroke : Svg.Size frame := .px 1) : Svg frame :=
  let total_points := hilbert_length i
  let scale := (2^i : Nat).toFloat

  -- Generate all line segments
  let lineElements := (List.range (total_points - 1)).map (fun j =>
    let (x1, y1) := hilbert_curve i j
    let (x2, y2) := hilbert_curve i (j+1)

    -- Scale points to fit in the frame
    let p1 := (x1.toFloat / scale * 2 - 1, y1.toFloat / scale * 2 - 1)
    let p2 := (x2.toFloat / scale * 2 - 1, y2.toFloat / scale * 2 - 1)

    line p1 p2 |>.setStroke (0., 0., 1.) stroke)

  { elements := lineElements.toArray }

-- Example: Display a Hilbert curve of order 2
#html (hilbert_curve_svg 2).toHtml
#html (hilbert_curve_svg 3).toHtml -- Looks good

/--
  Create an SVG visualization of two Hilbert curves of different orders.
-/
def hilbert_curve_with_points (i : ℕ) (stroke : Svg.Size frame := .px 3) : Svg frame :=
  let total_points := hilbert_length i
  let scale := (2^i : Nat).toFloat

  -- Generate all line segments
  let lineElements := (List.range (total_points - 1)).map (fun j =>
    let (x1, y1) := hilbert_curve i j
    let (x2, y2) := hilbert_curve i (j+1)

    -- Scale points to fit in the frame
    let p1 := (x1.toFloat / scale * 2 - 1, y1.toFloat / scale * 2 - 1)
    let p2 := (x2.toFloat / scale * 2 - 1, y2.toFloat / scale * 2 - 1)

    line p1 p2 |>.setStroke (0., 0., 1.) stroke)

  -- Generate squares at each coordinate
  let squareElements := (List.range total_points).map (fun j =>
    let (x, y) := hilbert_curve i j
    -- Scale point to fit in the frame
    let p_center := (x.toFloat / scale * 2 - 1, y.toFloat / scale * 2 - 1)
    let (px, py) := p_center
    let side_half := 0.9 / scale

    -- Define the four vertices of the square
    let points_abs : Array (Float × Float) := #[
      (px - side_half, py - side_half), -- bottom-left
      (px + side_half, py - side_half), -- bottom-right
      (px + side_half, py + side_half), -- top-right
      (px - side_half, py + side_half)  -- top-left
    ]
    let points : Array (Point frame) := points_abs.map (fun p => Point.abs p.1 p.2)

    polygon points
      |>.setFill (1.0,0.8,0.8)
      |>.setId s!"square{j}")

  { elements := (squareElements ++ lineElements).toArray }

#html (hilbert_curve_with_points 0).toHtml
#html (hilbert_curve_with_points 1).toHtml
#html (hilbert_curve_with_points 2).toHtml

def compare_hilbert_curves (i j : ℕ)
  (stroke1 : Svg.Size frame := .px 4)
  (stroke2 : Svg.Size frame := .px 2) : Svg frame :=
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
    line p1 p2 |>.setStroke (1., 0., 0.) stroke1)

  -- Generate line segments for the second curve (blue)
  let lineElements_j := (List.range (total_points_j - 1)).map (fun k =>
    let (x1, y1) := hilbert_curve j k
    let (x2, y2) := hilbert_curve j (k+1)
    let p1 := (x1.toFloat / scale_j * 2 - 1, y1.toFloat / scale_j * 2 - 1)
    let p2 := (x2.toFloat / scale_j * 2 - 1, y2.toFloat / scale_j * 2 - 1)
    line p1 p2 |>.setStroke (0.0, 0.5, 1.0) stroke2)

  -- Generate points at each coordinate
  let pointElements_i := (List.range total_points_i).map (fun j =>
    let (x, y) := hilbert_curve i j
    -- Scale point to fit in the frame
    let p := (x.toFloat / scale_i * 2 - 1, y.toFloat / scale_i * 2 - 1)
    circle p (.abs 0.05) |>.setFill (1.,0.,0.) |>.setId s!"point{j}")

  -- Generate points at each coordinate
  let pointElements_j := (List.range total_points_j).map (fun k =>
    let (x, y) := hilbert_curve j k
    -- Scale point to fit in the frame
    let p := (x.toFloat / scale_j * 2 - 1, y.toFloat / scale_j * 2 - 1)
    circle p (.abs 0.025) |>.setFill (0.0,0.5,1.0) |>.setId s!"point{k}")

  { elements := (lineElements_i ++ pointElements_i ++ lineElements_j ++ pointElements_j ).toArray }

-- Example: Compare Hilbert curves of order 2 and 3
#html (compare_hilbert_curves 2 3).toHtml
#html (compare_hilbert_curves 3 4).toHtml

/--
  Create an SVG visualization of the i-th order Hilbert curve,
  representing each segment H(n) as a square region [H(n), H(n) + (1,1)].
-/
def hilbert_curve_squares_svg (i : ℕ) : Svg frame :=
  let total_points := hilbert_length i
  -- total_points is always at least 1 for Nat i, as (2^i)^2 >= 1
  -- So, no need to check for total_points == 0.

  let scale_h := (2^i : Nat).toFloat -- This is N_side, e.g., for i=1, scale_h=2.0

  let squareElements := (List.range total_points).map (fun n =>
    let (xh_nat, yh_nat) := hilbert_curve i n
    let xh := xh_nat.toFloat
    let yh := yh_nat.toFloat

    -- Calculate SVG coordinates for the four corners of the square.
    -- The Hilbert curve coordinates (xh, yh) are from [0, scale_h - 1].
    -- We map this to [-1, 1] in the SVG's abstract coordinate system.
    -- A square corresponding to H(n) is [xh, xh+1] x [yh, yh+1] in Hilbert space.

    -- Bottom-left corner of the square
    let x_bl := xh / scale_h * 2.0 - 1.0
    let y_bl := yh / scale_h * 2.0 - 1.0
    -- Top-right corner of the square
    let x_tr := (xh + 1.0) / scale_h * 2.0 - 1.0
    let y_tr := (yh + 1.0) / scale_h * 2.0 - 1.0

    -- Define the four vertices of the polygon (square)
    -- P0: bottom-left, P1: bottom-right, P2: top-right, P3: top-left
    let points_abs : Array (Float × Float) := #[
      (x_bl, y_bl), (x_tr, y_bl), (x_tr, y_tr), (x_bl, y_tr)
    ]
    -- Coerce to Array (Point frame)
    let points : Array (Point frame) := points_abs.map (fun p => Point.abs p.1 p.2)

    -- Determine color based on n (normalized index along the curve)
    let hue := n.toFloat / total_points.toFloat
    let saturation := 1.0
    let lightness := 0.5
    let colorRGB := hslToRgb hue saturation lightness
    let color : Color := colorRGB -- Uses the Coe instance (Float×Float×Float) -> Color

    polygon points
      |>.setFill color
      --|>.setStroke (0.0, 0.0, 0.0) (.px 1) -- Black border, 1 pixel wide
      |>.setId s!"square{n}"
  )
  { elements := squareElements.toArray }

-- Example: Display Hilbert curve squares for order 0 (a single square)
#html (hilbert_curve_squares_svg 0).toHtml
#html (hilbert_curve_squares_svg 1).toHtml
#html (hilbert_curve_squares_svg 2).toHtml
#html (hilbert_curve_squares_svg 3).toHtml
#html (hilbert_curve_squares_svg 6).toHtml

private def displacement_plot_frame : Frame where
  xmin   := -0.1
  ymin   := -1.1
  xSize  := 1.2
  width  := 400
  height := Int64.toNatClampNeg <| Float.toInt64 <| 400 * 2.2 / 1.2
    -- height to make y_size = 2.2 if x_size = 1.2 and width = 400

/--
  Generates data for the displacement plot.
  Returns a list of (t, vx, vy) tuples, where:
  - t = k_offset / (hilbert_length i)
  - vx = (h_x(n_idx + k_offset) - h_x(n_idx)) / 2^i
  - vy = (h_y(n_idx + k_offset) - h_y(n_idx)) / 2^i
-/
def generate_displacement_data (i : Nat) (n_idx : Nat) : List (Float × Float × Float) :=
  let N_side := 2^i
  let M_len := hilbert_length i
  if M_len == 0 then [] else -- Should not happen for Nat i as 2^i is always >= 1
  let scale_factor := N_side.toFloat
  let (x_start, y_start) := hilbert_curve i n_idx
  let x_start_f := x_start.toFloat
  let y_start_f := y_start.toFloat

  (List.range M_len).map (fun k_offset =>
    let t_val := k_offset.toFloat / M_len.toFloat
    let (x_curr, y_curr) := hilbert_curve i (n_idx + k_offset)
    let vx := (x_curr.toFloat - x_start_f) / scale_factor
    let vy := (y_curr.toFloat - y_start_f) / scale_factor
    (t_val, vx, vy))



open Lean ProofWidgets Recharts
open scoped ProofWidgets.Jsx

/--
  Creates a Recharts line plot for the displacement data (vx, vy) against t,
  generated by `generate_displacement_data`.

  Parameters:
  - `i`: Order of the Hilbert curve. Must be greater than 0 for a meaningful plot.
  - `n_idx`: Starting index on the Hilbert curve for displacement calculation.
  - `chartWidth`: Optional. Width of the plot in pixels. Defaults to 400.
  - `chartHeight`: Optional. Height of the plot in pixels. Defaults to 400.
-/
def DisplacementPlot (i : Nat) (n_idx : Nat) (chartWidth := 400) (chartHeight := 400) : Html :=
  if i == 0 then
    Html.text "Displacement plot is not very informative for i=0, as the curve is a single point at the origin, resulting in zero displacement."
  else
    let dataList := generate_displacement_data i n_idx
    -- For i > 0, hilbert_length i is (2^i)^2, which is at least 4.
    -- So, dataList will contain at least 4 points.
    let jsonData : Array Json :=
      dataList.toArray |> Array.map (fun (t, vx, vy) =>
        json% {t: $(toJson t), vx: $(toJson vx), vy: $(toJson vy), max: $(toJson (max (vx.abs) (vy.abs))),
        sqrt: $(toJson <| 2*(t.sqrt))
        }
      );
    <LineChart width= {chartWidth} height={chartHeight} data={jsonData} >
      <XAxis dataKey?="t" domain?={#[toJson 0, toJson 1]} type={.number} />
      <YAxis domain?={#[toJson (-1.1), toJson 1.1]} allowDataOverflow={false} type={.number} />
      <Line type={.monotone} dataKey="max" stroke="#ffcaff" dot?={Bool.false} />
      <Line type={.monotone} dataKey="sqrt" stroke="#0abe0f" dot?={Bool.false} />
    </LineChart>

-- Example usage of the DisplacementPlot:

-- Plot for Hilbert curve of order 2, starting at index 0
#html DisplacementPlot 2 0

-- Plot for Hilbert curve of order 3, starting at index 10
-- This will show how displacement changes relative to the point `hilbert_curve 3 10`.
#html DisplacementPlot 3 0
#html DisplacementPlot 6 0

-- Example for i=1, starting at index 0.
-- hilbert_length 1 is 4. Data points for k_offset = 0, 1, 2, 3.
#html DisplacementPlot 1 0

-- This will display the message for i=0.
#html DisplacementPlot 0 0

end HilbertCurve

namespace ProofWidgets

def escapeString : Lean.Json → String
  | .null => "null"
  | .bool (b : Bool) => "\"" ++ toString b ++ "\""
  | .num n => "\"" ++ toString n ++ "\""
  | .str (s : String) => "\"" ++ s ++ "\""
  | .arr _ => "array"
  | .obj _ => "obj"

partial def Html.toString : Html → String
  | Html.element tag attrs children =>
      let mappedAttrs := attrs.map (fun (k, v) => " " ++ k ++ "=" ++ (escapeString v))
      let attrsStr := String.join mappedAttrs.toList
      let childrenStr := String.join (children.map Html.toString).toList
      s!"<{tag}{attrsStr}>{childrenStr}</{tag}>"
  | Html.text s => s
  | Html.component _ _ _ children =>
      let childrenStr := String.join (children.map Html.toString).toList
      s!"<component>{childrenStr}</component>"


end ProofWidgets

namespace HilbertCurve

-- Example: Save the comparison of Hilbert curves of order 2 and 3 to an SVG file
def saveComparisonToFile (i j : ℕ) (fileName : String) : IO Unit := do
  let svgString := (compare_hilbert_curves i j).toHtml.toString
  let filePath : System.FilePath := fileName
  IO.FS.writeFile filePath svgString
  IO.println s!"Saved Hilbert curve comparison to {filePath}"

end HilbertCurve

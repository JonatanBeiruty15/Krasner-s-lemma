from manim import *

class Sierpinski3Adic(Scene):
    def construct(self):
        num_iterations = 5
        base_length = 6
        base_stroke_width = 6
        number_scale_range = 200
        shift_scale = 0.5

        number_line = NumberLine(
            x_range=[-number_scale_range, number_scale_range, 5],
            length=20,
            include_ticks=True,
            include_numbers=True,
            font_size=24
        )
        number_line.to_edge(UP).shift(DOWN * 0.3)

        visible_labels = VGroup()
        for number in number_line.numbers:
            val = int(number.get_value())
            if val in [-100, 0, 100]:
                visible_labels.add(number)
            else:
                number.set_opacity(0)

        self.play(Create(VGroup(number_line, visible_labels)))

        z_label = MathTex("\\mathbb{Z}", font_size=36)
        z_label.next_to(number_line, UP, buff=0.2)
        self.play(Write(z_label))

        A = LEFT * base_length / 2
        B = RIGHT * base_length / 2
        height = base_length * (3**0.5) / 2
        C = UP * height
        centroid = (A + B + C) / 3
        shift = -centroid + DOWN * 2
        A += shift
        B += shift
        C += shift

        base_triangle = Polygon(A, B, C, color=WHITE, stroke_width=base_stroke_width)
        base_triangle.scale(0.6)
        self.play(Create(base_triangle))

        triangle_levels = [[(base_triangle, '')]]
        triangle_positions = [(C, "0"), (B, "1"), (A, "2")]
        self.wait()

        vertices_labels = []
        for order in range(1, num_iterations + 1):
            new_level = []
            new_positions = []
            created_triangles = []
            red_to_white_anims = []
            vertices_labels_new_order = []

            self.play(*[FadeOut(triangle, run_time=0.05) for triangle, _ in triangle_levels[order - 1]])

            for triangle, label in triangle_levels[order - 1]:
                A, B, C = triangle.get_vertices()
                AB = interpolate(A, B, 0.5)
                BC = interpolate(B, C, 0.5)
                CA = interpolate(C, A, 0.5)

                parent_centroid = (A + B + C) / 3

                def centroid(*pts):
                    return sum(pts) / len(pts)

                center_top = centroid(A, AB, CA)
                center_right = centroid(AB, B, BC)
                center_left = centroid(CA, BC, C)

                decay_adjusted_scale = shift_scale * (0.9 ** (order - 1))
                t_top_shift = (center_top - parent_centroid) * decay_adjusted_scale
                t_right_shift = (center_right - parent_centroid) * decay_adjusted_scale
                t_left_shift = (center_left - parent_centroid) * decay_adjusted_scale

                stroke = base_stroke_width * (0.6 ** order)

                t_top = Polygon(A + t_top_shift, AB + t_top_shift, CA + t_top_shift, color=RED, stroke_width=stroke)
                t_right = Polygon(AB + t_right_shift, B + t_right_shift, BC + t_right_shift, color=RED, stroke_width=stroke)
                t_left = Polygon(CA + t_left_shift, BC + t_left_shift, C + t_left_shift, color=RED, stroke_width=stroke)

                up_label = label + '0'
                right_label = label + '1'
                left_label = label + '2'

                new_level.extend([(t_top, up_label), (t_right, right_label), (t_left, left_label)])

                top_vertices_labels = [(A + t_top_shift, up_label + '2'), (AB + t_top_shift, up_label + '1'), (CA + t_top_shift, up_label + '0')]
                right_vertices_labels = [(AB + t_right_shift, right_label + '2'), (B + t_right_shift, right_label + '1'), (BC + t_right_shift, right_label + '0')]
                left_vertices_labels = [(CA + t_left_shift, left_label + '2'), (BC + t_left_shift, left_label + '1'), (C + t_left_shift, left_label + '0')]

                vertices_labels_new_level = [top_vertices_labels, right_vertices_labels, left_vertices_labels]
                vertices_labels_new_order.append(vertices_labels_new_level)

                created_triangles.extend([t_top, t_right, t_left])
                red_to_white_anims.extend([
                    t_top.animate.set_color(WHITE),
                    t_right.animate.set_color(WHITE),
                    t_left.animate.set_color(WHITE)
                ])

            vertices_labels.append(vertices_labels_new_order)
            self.play(*[Create(tri) for tri in created_triangles])
            self.play(*red_to_white_anims, run_time=0.5)

            triangle_levels.append(new_level)
            triangle_positions.extend(new_positions)
            self.wait(0.3)

        self.wait()
        self.triangle_positions = triangle_positions

        flat_labels = [pair for triangle in vertices_labels[-1] for pair in triangle]
        flat_labels = [pair for triangle in flat_labels for pair in triangle]
        self.vertices_labels = flat_labels

        target_number = 15
        digits = []
        n = target_number
        for _ in range(num_iterations + 1):
            digits.append(n % 3)
            n //= 3
        label = ''.join(str(d) for d in digits)
        print(f'this is the {target_number} label: {label}')

        match_point = None
        for pt, lbl in self.vertices_labels:
            if lbl == label:
                match_point = pt
                match_marker = Dot(match_point, color=PINK, radius=0.05)
                self.add(match_marker)
                break

        if match_point is None:
            print(f"Label {label} not found.")
            return

        label_text = Text('15 = 0 + 2·3 + 1·3²', font_size=28)
        label_text.next_to(number_line, DOWN, buff=0.5)
        self.play(Write(label_text))
        self.wait(1)
        self.play(FadeOut(label_text))

        dot = Dot(color=YELLOW, radius=0.05)
        number_line_x = number_line.number_to_point(target_number)
        dot.move_to(number_line_x)
        self.add(dot)
        self.play(dot.animate.move_to(match_point), run_time=2)
        self.wait()

        all_dots = []
        animations = []
        for n in range(-number_scale_range, number_scale_range + 1):
            val = abs(n)
            digits = []
            for _ in range(num_iterations + 1):
                digits.append(val % 3)
                val //= 3
            label = ''.join(str(d) for d in digits)

            match_point = None
            for pt, lbl in self.vertices_labels:
                if lbl == label:
                    match_point = pt
                    break
            if match_point is None:
                continue

            color = RED if n % 3 == 0 else YELLOW if n % 3 == 1 else BLUE
            dot2= Dot(color=color, radius=0.025)
            dot2.move_to(number_line.number_to_point(n))
            all_dots.append(dot2)
            animations.append(dot2.animate.move_to(match_point))

        self.add(*all_dots)
        self.wait(0.5)
        self.play(*animations, run_time=3)
        self.wait()

        z3_label = MathTex("\\mathbb{Z}_3", font_size=36)
        final_layer_group = VGroup(*[tri for tri, _ in triangle_levels[-1]])
        z3_label.next_to(final_layer_group, LEFT, buff=0.6)
        self.play(Write(z3_label))
        self.wait()

        self.play(FadeOut(number_line), FadeOut(match_marker), FadeOut(visible_labels),FadeOut(dot) ,FadeOut(z_label), FadeOut(z3_label), *[FadeOut(dot) for dot in all_dots])

        bounding_circle = Circle(color=WHITE).surround(final_layer_group, buffer_factor=1.2)
        triangle_scene = VGroup(final_layer_group, bounding_circle)
        self.play(Create(bounding_circle))
        self.play(triangle_scene.animate.scale(0.3).to_corner(LEFT + DOWN))
        

        final_equation = MathTex(
        r"\mathbb{Z}_3 \times \mathbb{Z}_3^* \mathbin{/} \sim \; := \; \mathrm{Frac}(\mathbb{Z}_3) \; := \; \mathbb{Q}_3",
            font_size=42)
        
        final_equation.move_to(ORIGIN)  # Center it

        self.play(Write(final_equation))
        self.wait()


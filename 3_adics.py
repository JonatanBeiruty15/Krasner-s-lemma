from manim import *

class Sierpinski3Adic(Scene):
    def construct(self):
        num_iterations = 5
        base_length = 6
        base_stroke_width = 6
        number_scale_range = 100
        # Add number line at the top
        number_line = NumberLine(
            x_range=[-number_scale_range, number_scale_range, 5],
            length=10,
            include_ticks=True,
            include_numbers=True,
            font_size=24
        )
        number_line.to_edge(UP)


        # Hide all labels except -50, 0, 50
        visible_labels = VGroup()
        for number in number_line.numbers:
            if int(number.get_value()) in [-number_scale_range, 0, number_scale_range]:
                visible_labels.add(number)
            else:
                number.set_opacity(0)  # hide others

        # Animate number line + visible labels together
        self.play(Create(VGroup(number_line, visible_labels)))

        # Construct initial equilateral triangle
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

        triangle_levels = [[(base_triangle,'')]]

        
        triangle_positions = [
            (C, "0"),
            (B, "1"),
            (A, "2")
        ]

        self.wait()

        

        vertices_labels = []
        for order in range(1, num_iterations+1):
            new_level = []
            new_positions = []

            created_triangles = []
            red_to_white_anims = []
            
            vertices_labels_new_order = []
            for triangle , label in triangle_levels[order - 1]: 
                
                A, B, C = triangle.get_vertices()
                AB = interpolate(A, B, 0.5)
                BC = interpolate(B, C, 0.5)
                CA = interpolate(C, A, 0.5)

                stroke = base_stroke_width * (0.6 ** order)

                # Create red sub-triangles
                t_top = Polygon(A, AB, CA, color=RED, stroke_width=stroke)
                t_right = Polygon(AB, B, BC, color=RED, stroke_width=stroke)
                t_left = Polygon(CA, BC, C, color=RED, stroke_width=stroke)


                up_label = label + '0'
                right_label = label + '1'
                left_label = label + '2'

                new_level.extend([(t_top,up_label), (t_right,right_label), (t_left,left_label)])
                
                top_vertices_labels = [(A,up_label+'2'),(AB,up_label+'1') , (CA,up_label + '0')]
                right_vertices_labels = [(AB,right_label+'2'),(B,right_label+'1') , (BC,right_label + '0')]
                left_vertices_labels = [(CA,left_label+'2'),(BC,left_label+'1') , (C,left_label + '0')]

                vertices_labels_new_level = [top_vertices_labels,right_vertices_labels,left_vertices_labels]
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


   
                # --- Compute the 3-adic expansion of 13 ---
        target_number = 15
        digits = []
        n = target_number
        for _ in range(num_iterations+1):
            digits.append(n % 3)
            n //= 3
        label = ''.join(str(d) for d in digits)  # reversed order for p-adics
        print(f'this is the {target_number} label: {label}')
        # --- Find matching triangle position ---
        match_point = None
        for pt, lbl in self.vertices_labels:
            print(lbl)
            if lbl == label:
                match_point = pt

                # Add a pink dot at the matched triangle vertex
                match_marker = Dot(match_point, color=PINK,radius=0.05)
                self.add(match_marker)
                break

        if match_point is None:
            print(f"Label {label} not found.")
            return

        # --- Show the 3-adic expansion as text ---
        label_text = Text('15 = 0 + 2·3 + 1·3²', font_size=28)
        label_text.next_to(number_line, DOWN, buff=0.5)  # place it under the number line
        self.play(Write(label_text))
        self.wait(1)

        self.play(FadeOut(label_text))
        # --- Animate a dot flying from 13 on the number line to match_point ---
        dot = Dot(color=YELLOW,radius=0.05)
        number_line_x = number_line.number_to_point(target_number)
        dot.move_to(number_line_x)

        self.add(dot)
        self.play(dot.animate.move_to(match_point), run_time=2)
        self.wait()


        # --- Project all numbers onto triangle: create dots first ---
        all_dots = []
        animations = []

        for n in range(-number_scale_range, number_scale_range + 1):
            val = abs(n)
            digits = []
            for _ in range(num_iterations + 1):
                digits.append(val % 3)
                val //= 3
            label = ''.join(str(d) for d in digits)

            # Find matching triangle vertex
            match_point = None
            for pt, lbl in self.vertices_labels:
                if lbl == label:
                    match_point = pt
                    break
            if match_point is None:
                continue  # skip if not found

            # Color based on n mod 3
            if n % 3 == 0:
                color = RED
            elif n % 3 == 1:
                color = YELLOW
            else:
                color = BLUE

            # Create small dot on the number line
            dot = Dot(color=color, radius=0.025)
            dot.move_to(number_line.number_to_point(n))
            all_dots.append(dot)

            # Prepare the animation from number line to triangle point
            animations.append(dot.animate.move_to(match_point))

        # --- Add all the dots at once to the number line ---
        self.add(*all_dots)
        self.wait(0.5)

        # --- Animate all the dots flying into the triangle at once ---
        self.play(*animations, run_time=3)
        self.wait()
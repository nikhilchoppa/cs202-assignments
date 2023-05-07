import os
import csv
from compiler import run_compiler


def generate_dataset(input_folder='tests'):
    dataset = []

    for file_name in os.listdir(input_folder):
        print(file_name)
        if not file_name.endswith('.py'):
            continue

        with open(os.path.join(input_folder, file_name), 'r') as file:
            program = file.read()

            # Compile with graph coloring method
            _, _, gc_exec_time = run_compiler(program, 'graph_coloring')

            # Compile with linear scan method
            _, _, ls_exec_time = run_compiler(program, 'linear_scan')

        dataset.append((file_name, gc_exec_time, ls_exec_time))

    return dataset


def write_dataset_to_csv(dataset, output_file='dataset.csv'):
    with open(output_file, 'w', newline='') as csvfile:
        csv_writer = csv.writer(csvfile)
        csv_writer.writerow(['file_name', 'graph_coloring_exec_time', 'linear_scan_exec_time'])
        for data in dataset:
            csv_writer.writerow(data)


if __name__ == '__main__':
    dataset = generate_dataset()
    write_dataset_to_csv(dataset)

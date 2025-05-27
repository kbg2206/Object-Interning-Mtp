public class Input1 {
    int a;
    int b;

    Input1(int x) {
        a = x;
        b = 2 * x;
    }

    Input1() {
        a = 4;
        b = 8;
    }

    Boolean equals(Input1 obj) {
        if (this.a == obj.a && this.b == obj.b)
            return true;
        

        return false;
    }

    public static void main(String[] args) {
        long startTime = System.nanoTime();

        Input1[] arr = new Input1[100000];

        for (int i = 0; i < 100000; ++i) {
            if (i % 2 == 0) {
                arr[i] = new Input1(4);
            } else {
                arr[i] = new Input1();
            }
        }

        for (long i = 0; i < 1_000_000_000_0L; i += 2) {
            int index1 = (int)(i % 10000);
            int index2 = (int)((i + 1) % 10000);

            if (arr[index1].equals(arr[index2])) {
                // System.out.println("Same");
            } else {
                // System.out.println("Different");
            }
        }

        long endTime = System.nanoTime();
        long duration = endTime - startTime;
        System.out.println("Execution time: " + duration / 1e9 + " s");
    }
}

class A {
    int a;
    String s;

    A(int x, String z) {
        a = 2 * x;
        s = z;
    }

}

class Benchmark4 extends A {
    int a;
    int b;
    A o1;

    Benchmark4(int x, int y, String z) {
        super(2 * x + y, z);
        a = 3 * x;
        b = 4 * y;
        o1 = new A(a, z);
    }

    public static void main(String[] args) {
        long startTime = System.currentTimeMillis();

        Benchmark4[] benchmarkArray = new Benchmark4[10000];

        for (int i = 0; i < 10000; ++i) {

            benchmarkArray[i] = new Benchmark4(8 * i, 10 * i, "Hello");
        }

        for (int i = 0; i < 10000; ++i) {
            for (int j = i + 1; j < 10000; ++j) {
                if (benchmarkArray[i].equals(benchmarkArray[j])) {
                    // System.out.println("Objects are equal ");
                } else {
                    // System.out.println("Objects are not equal ");
                }
            }
        }

        long endTime = System.currentTimeMillis();

        System.out.println("Time taken: " + (endTime - startTime) + " ms");
    }
}

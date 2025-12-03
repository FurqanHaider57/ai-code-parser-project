/*
 * Sample C Code for Simulink Conversion
 * File: sample_code.c
 */

#include <stdio.h>
#include <math.h>

// Function 1: Basic arithmetic operations
void basic_operations() {
    int a=5,b=10;
    result = a + b;
    myVar += myConst1 - myConst2 * myConst3;
    myVar -= myConst4;
    output = (gain1 + gain2) * input - offset;
    output *= scale_factor;
}

// Function 2: PID Controller
void pid_controller() {
    error = setpoint - feedback;
    integral += error * dt;
    derivative = (error - prev_error) / dt;
    output = kp * error + ki * integral + kd * derivative;
    prev_error = error;
}

int main() {
    printf("Sample C code for conversion\n");
    return 0;
}
